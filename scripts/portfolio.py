#!/usr/bin/env python3
"""portfolio.py: virtual and real portfolio experiments for the ltts benchmarks.

The script
  1. uses the cvc5 binary given by --cvc5 (normally the build of this
     checkout, e.g. --cvc5 build/bin/cvc5 or --cvc5 build/bin); without
     --cvc5 it clones and builds the branch of this PR (cycle-ext-cyclic of
     mudathirmahgoub/cvc5) in the work directory; an existing clone is reused
     (fetched only if the pinned commit is missing) and an existing build of
     the same commit is not rebuilt; the official cvc5 releases do not know
     rel.cyclic, so a release download is not an option. Every
     configuration's options are checked against the binary before anything
     is run;
  2. obtains the benchmarks (relational-solver-benchmarks, by default at the
     head of rachelcleaveland/relational-solver-benchmarks#2, which states
     acyclicity with rel.cyclic) by cloning the repository, unless already
     present (no network access then), or uses a local directory given with
     --benchmarks-dir (no git involved at all). Only files WITHOUT an active
     (set-option :finite-model-find true) line are used; configurations that
     want finite model finding pass --finite-model-find on the command line,
     which cvc5 treats identically. Checkouts where benchmarks-ltts still
     switches it on are handled by using their benchmarks-ltts-nofmf
     directory (next to or inside benchmarks-ltts) instead;
  3. runs the seven configurations of the portfolio in one or both modes.

Definitions
  virtual portfolio (also called the virtual best solver, VBS)
      Every (benchmark, configuration) pair is run on its own, one process at
      a time, each with the full time limit. For a benchmark the portfolio's
      answer is the answer of the configuration that solved it fastest and the
      portfolio's time is the MINIMUM of the configurations' times. Nothing
      runs concurrently, so the times are free of contention; the VBS is the
      lower bound for any parallel portfolio of the same configurations.
      The script also reports the "cascade" time, i.e. what trying the
      configurations one after another (each with the full limit, in the
      listed order) would have cost: the SUM of the failed attempts plus the
      successful one. That is the other meaning sometimes attached to
      "sequential portfolio"; the minimum, not the sum, is the virtual
      portfolio.
  real portfolio
      For every benchmark all configurations start at the same moment as
      separate processes. The first process that prints sat or unsat wins:
      its answer and wall-clock time are the portfolio's, and the remaining
      processes are killed. Processes that end with unknown, an error or a
      time limit do not win; if no process wins the benchmark is unsolved.
      The total CPU time of all processes is recorded as well.

Typical use (from the root of the cvc5 checkout)
  python3 scripts/portfolio.py --cvc5 build/bin/cvc5 --mode both --timeout 300 --jobs 6
  python3 scripts/portfolio.py --cvc5 build/bin/cvc5 --mode real --timeout 60
  python3 scripts/portfolio.py --cvc5 build/bin/cvc5 --benchmarks-dir /path/to/benchmarks-ltts --mode virtual
  python3 scripts/portfolio.py --cvc5 build/bin/cvc5 --mode cvc5-portfolio   # what cvc5's own --use-portfolio does

Requirements: python3 (>= 3.8), git (unless --cvc5 and --benchmarks-dir
are both given); for building cvc5: cmake, a C++17
compiler, python3 modules tomli and pyparsing, and network access for
./configure.sh --auto-download.
"""

import argparse
import datetime
import glob
import json
import os
import re
import resource
import shutil
import signal
import subprocess
import sys
import time
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor

# --------------------------------------------------------------------------
# Defaults
# --------------------------------------------------------------------------

CVC5_REPO = "https://github.com/mudathirmahgoub/cvc5.git"
CVC5_BRANCH = "cycle-ext-cyclic"
CVC5_REV = "4db5c57b0a"  # rachelcleaveland/cvc5#9 (rel.cyclic), 2026-10-09

# rachelcleaveland/relational-solver-benchmarks#2: the benchmarks with
# rel.is-functional (#1) and rel.cyclic. For the rel.acyclic files of #1 use
# --benchmarks-rev f5efdad8e216bfa35549f038b8f6df83de36d35e (with a cvc5 that
# knows rel.acyclic and --configs-file scripts/configs-acyclic.json).
BENCH_REPO = "https://github.com/mudathirmahgoub/relational-solver-benchmarks.git"
BENCH_REV = "e4a4f7e01b90c80e7a796e02c65eea024f999b58"
BENCH_SUBDIR = "benchmarks-ltts"
# Where the no-FMF files live, relative to the repository root, in order of
# preference: benchmarks-ltts itself (when its files do not enable finite
# model finding), or the separate no-FMF directory (inside or next to
# benchmarks-ltts, as at BENCH_REV).
NOFMF_CANDIDATES = [BENCH_SUBDIR, BENCH_SUBDIR + "/benchmarks-ltts-nofmf", "benchmarks-ltts-nofmf"]
BENCH_SET_FILE = "benchmark_set_ltts"    # basenames only, so it applies whichever directory is used
FMF_LINE = re.compile(r"^\(set-option\s+:finite-model-find\s+true\)", re.M)

# The configurations of the portfolio. All of them run the no-FMF files;
# finite model finding is switched on per configuration with FMF below
# (cvc5 treats --finite-model-find and the set-option line identically).
#   default, fmf-unsat, nofmf-unsat, stoponly: the recipes of PR #4;
#   *-rules, *-hammer: the same recipes plus the inference rules of PR #6
#     (closure induction, no prenexing).
# Before rel.cyclic the rules also included --rels-acyclic-flatten-union,
# which rel.cyclic does always, and --rels-functional-axioms, a preprocessing
# pass that is redundant with rel.is-functional (both options are removed);
# configs-acyclic.json has those configurations, for builds that know
# rel.acyclic.
FMF = ["--finite-model-find"]
PR4_FMF = FMF + ["--e-matching", "--inst-when=full-delay",
                 "--rels-acyclic-anchor=inclusion", "--rels-acyclic-backward-chords"]
PR4_NOFMF = ["--rels-acyclic-anchor=inclusion", "--inst-when=full-delay",
             "--rels-acyclic-backward-chords"]
PR6_RULES = ["--prenex-quant=none", "--rels-tc-subset"]
CONFIGS = OrderedDict([
    ("default", dict(
        opts=FMF,
        desc="finite model finding, otherwise cvc5 defaults (what the published file does)")),
    ("fmf-unsat", dict(
        opts=PR4_FMF,
        desc="PR #4: finite model finding + eager instantiation + inclusion anchor + backward chords")),
    ("nofmf-unsat", dict(
        opts=PR4_NOFMF,
        desc="PR #4: the same recipe without finite model finding")),
    ("stoponly", dict(
        opts=FMF + ["--decision=stoponly"],
        desc="PR #4: SAT decisions by MiniSat, justification engine only stops early")),
    ("fmf-unsat-rules", dict(
        opts=PR4_FMF + PR6_RULES + ["--rels-tc-down-lazy"],
        desc="PR #6: fmf-unsat + closure induction, no prenexing, lazy closure split")),
    ("nofmf-unsat-rules", dict(
        opts=PR4_NOFMF + PR6_RULES + ["--rels-tc-down-lazy"],
        desc="PR #6: nofmf-unsat + the same rules and lazy closure split")),
    ("nofmf-unsat-hammer", dict(
        opts=PR4_NOFMF + PR6_RULES + ["--rels-acyclic-hammer"],
        desc="PR #6: nofmf-unsat + the same rules, no closure split (unsat only)")),
])

# Hand-verified expected answers for benchmarks-ltts at de01351 and later
# (README.md, "Expected results"). Used only to flag wrong answers.
EXPECTED = {
    "sc-1-th": "unsat", "sc-1-th-just-rf": "unsat", "sc-1-th-no-ltts": "sat",
    "sc-2-th": "unsat", "sc-2-th-just-rf": "unsat",
    "plsc-1-th": "unsat", "plsc-1-th-just-rf": "unsat", "plsc-1-th-no-ltts": "sat",
    "plsc-2-th": "unsat", "plsc-2-th-just-rf": "unsat",
    "tso-1-th": "unsat", "tso-1-th-just-rf": "unsat", "tso-1-th-no-ltts": "sat",
    # tso-2-th and tso-2-th-just-rf (added 2026-10-10) have the same shape as
    # the other *-th files, the templates asserted and an execution the model
    # forbids requested, so unsat is the expected answer by construction; it
    # has not yet been confirmed by a solver run (every configuration timed
    # out at 120 s on the pr-9 build).
    "tso-2-th": "unsat", "tso-2-th-just-rf": "unsat",
}

HARD_TIMEOUT_GRACE = 30.0  # seconds after --tlimit before a process is killed
POLL_INTERVAL = 0.02       # seconds, real portfolio


def log(msg):
    print("[portfolio %s] %s" % (datetime.datetime.now().strftime("%H:%M:%S"), msg), flush=True)


def sh(cmd, cwd=None, logfile=None, check=True):
    """Run a command, append its output to logfile (if given), return the CompletedProcess."""
    log("$ " + " ".join(cmd) + (" (in %s)" % cwd if cwd else ""))
    if logfile:
        with open(logfile, "a") as f:
            f.write("$ " + " ".join(cmd) + "\n")
            f.flush()
            p = subprocess.run(cmd, cwd=cwd, stdout=f, stderr=subprocess.STDOUT)
    else:
        p = subprocess.run(cmd, cwd=cwd)
    if check and p.returncode != 0:
        raise SystemExit("command failed (%d): %s%s" % (
            p.returncode, " ".join(cmd), ("; see " + logfile) if logfile else ""))
    return p


# --------------------------------------------------------------------------
# Step 1: cvc5
# --------------------------------------------------------------------------

def check_options(binary, configs):
    """Run every configuration's options on an empty input so that an option
    the binary does not know fails here, once, instead of in every run."""
    bad = []
    for c in configs:
        p = subprocess.run([binary, "--lang=smt2"] + CONFIGS[c]["opts"], input="", capture_output=True,
                           text=True, timeout=60)
        out = (p.stdout + p.stderr).strip()
        if p.returncode != 0 or "Error in option parsing" in out:
            bad.append("  %s: %s" % (c, out.splitlines()[0] if out else "exit code %d" % p.returncode))
    if bad:
        raise SystemExit("%s rejects the options of %d configuration(s):\n%s\n(is the binary built from %s?)"
                         % (binary, len(bad), "\n".join(bad), CVC5_BRANCH))
    log("option check: all %d configurations accepted by %s" % (len(configs), binary))


def cvc5_version(binary):
    try:
        out = subprocess.run([binary, "--version"], capture_output=True, text=True, timeout=60)
        return (out.stdout + out.stderr).strip().splitlines()[0]
    except Exception as e:  # noqa: BLE001
        return "unavailable (%s)" % e


def git(repo, *argv, check=True):
    p = subprocess.run(["git", "-C", repo] + list(argv), capture_output=True, text=True)
    if check and p.returncode != 0:
        raise SystemExit("git %s failed in %s: %s" % (" ".join(argv), repo, p.stderr.strip()))
    return p.stdout.strip()


def has_commit(repo, rev):
    return subprocess.run(["git", "-C", repo, "cat-file", "-e", rev + "^{commit}"],
                          capture_output=True).returncode == 0


def ensure_checkout(repo, url, branch, rev, logfile=None):
    """Clone repo if missing; check out rev, fetching only if rev is not
    already present locally. Returns the full commit id of HEAD."""
    if not os.path.isdir(os.path.join(repo, ".git")):
        log("cloning %s%s" % (url, (" (branch %s)" % branch) if branch else ""))
        cmd = ["git", "clone", "--quiet"] + (["--branch", branch] if branch else []) + [url, repo]
        sh(cmd, logfile=logfile)
    else:
        log("found %s, not downloading it again" % repo)
    if rev and rev != "HEAD":
        if not has_commit(repo, rev):
            log("commit %s is not in the local clone; fetching" % rev)
            sh(["git", "-C", repo, "fetch", "--quiet", "origin"] + ([branch] if branch else []),
               logfile=logfile, check=False)
            if not has_commit(repo, rev):
                sh(["git", "-C", repo, "fetch", "--quiet", "origin", rev], logfile=logfile, check=False)
            if not has_commit(repo, rev):
                raise SystemExit("commit %s not found in %s" % (rev, url))
        if git(repo, "rev-parse", "HEAD") != git(repo, "rev-parse", rev + "^{commit}"):
            sh(["git", "-C", repo, "checkout", "--quiet", rev], logfile=logfile)
    elif branch and os.path.isdir(os.path.join(repo, ".git")) and rev == "HEAD":
        # explicit request for the branch tip: this is the only case that always fetches
        sh(["git", "-C", repo, "fetch", "--quiet", "origin", branch], logfile=logfile, check=False)
        sh(["git", "-C", repo, "checkout", "--quiet", "FETCH_HEAD"], logfile=logfile)
    return git(repo, "rev-parse", "HEAD")


def ensure_cvc5(args):
    if args.cvc5:
        binary = os.path.abspath(args.cvc5)
        if os.path.isdir(binary):  # e.g. build/bin: look for the binary inside
            binary = os.path.join(binary, "cvc5")
        if not (os.path.isfile(binary) and os.access(binary, os.X_OK)):
            raise SystemExit("--cvc5 %s is not an executable file" % binary)
        log("using cvc5 given on the command line: %s" % binary)
        return binary
    repo = os.path.join(args.workdir, "cvc5")
    build = os.path.join(repo, "build")
    binary = os.path.join(build, "bin", "cvc5")
    stamp = os.path.join(build, ".portfolio-built-rev")
    logfile = os.path.join(args.workdir, "cvc5-build.log")
    head = ensure_checkout(repo, args.cvc5_repo, args.cvc5_branch, args.cvc5_rev, logfile)
    built = open(stamp).read().strip() if os.path.isfile(stamp) else None
    if os.access(binary, os.X_OK) and built == head and not args.rebuild:
        log("found a build of %s: %s (not rebuilding)" % (head[:10], binary))
        return binary
    log("cvc5 source at %s; building (log: %s)" % (head[:10], logfile))
    configured = os.path.isfile(os.path.join(build, "CMakeCache.txt"))
    if args.rebuild and os.path.isdir(build):
        shutil.rmtree(build)
        configured = False
    if not configured:
        if os.path.isdir(build):  # incomplete configuration
            shutil.rmtree(build)
        # cvc5 renamed the optimised build type from 'production' to
        # 'unrestricted' in 2026; pick whichever this checkout understands.
        helptext = subprocess.run(["./configure.sh", "--help"], cwd=repo, capture_output=True, text=True).stdout
        build_type = "unrestricted" if "unrestricted" in helptext else "production"
        sh(["./configure.sh", build_type, "--auto-download", "--name=build"], cwd=repo, logfile=logfile)
    else:
        log("reusing the configured build directory (incremental build)")
    sh(["make", "-j%d" % args.build_jobs], cwd=build, logfile=logfile)
    if not os.access(binary, os.X_OK):
        raise SystemExit("build finished but %s is missing; see %s" % (binary, logfile))
    open(stamp, "w").write(head + "\n")
    log("built %s" % binary)
    return binary


# --------------------------------------------------------------------------
# Step 2: benchmarks
# --------------------------------------------------------------------------

def files_with_fmf(directory):
    """Basenames (without .smt2) of the files in DIRECTORY that switch finite model finding on."""
    return sorted(os.path.basename(f)[:-5] for f in glob.glob(os.path.join(directory, "*.smt2"))
                  if FMF_LINE.search(open(f, errors="replace").read()))


def find_nofmf_dir(root):
    """The first of NOFMF_CANDIDATES under ROOT that holds .smt2 files none of
    which enables finite model finding; None if there is no such directory."""
    for sub in NOFMF_CANDIDATES:
        d = os.path.join(root, sub)
        if glob.glob(os.path.join(d, "*.smt2")) and not files_with_fmf(d):
            return d
    return None


def local_benchmarks(path):
    """Resolve --benchmarks-dir. PATH is either the root of the benchmark
    repository or the directory holding the no-FMF .smt2 files itself.
    Returns (repo, bench_dir, rev); no git is required, the revision is
    taken from git only if PATH happens to be a checkout."""
    root = os.path.abspath(path)
    if not os.path.isdir(root):
        raise SystemExit("--benchmarks-dir %s is not a directory" % root)
    if glob.glob(os.path.join(root, "*.smt2")):
        repo, bench_dir = os.path.dirname(root), root
    else:
        bench_dir = find_nofmf_dir(root)
        if bench_dir is None:
            raise SystemExit("--benchmarks-dir %s contains neither .smt2 files nor a no-FMF directory (%s)"
                             % (root, ", ".join(NOFMF_CANDIDATES)))
        repo = root
    p = subprocess.run(["git", "-C", bench_dir, "rev-parse", "HEAD"], capture_output=True, text=True)
    rev = p.stdout.strip() if p.returncode == 0 and p.stdout.strip() else "local"
    log("using local benchmarks in %s (rev %s; nothing is cloned)" % (bench_dir, rev))
    return repo, bench_dir, rev


def ensure_benchmarks(args):
    if args.benchmarks_dir:
        repo, bench_dir, head = local_benchmarks(args.benchmarks_dir)
    else:
        repo = os.path.join(args.workdir, "relational-solver-benchmarks")
        head = ensure_checkout(repo, args.benchmarks_repo, None, args.benchmarks_rev)
        bench_dir = find_nofmf_dir(repo)
        if bench_dir is None:
            raise SystemExit("no directory of no-FMF benchmarks (%s) in %s" % (", ".join(NOFMF_CANDIDATES), repo))

    # Which files form the benchmark set: the repository's list if present
    # (it excludes plsc-2-th.new.smt2), otherwise every .smt2 that is not a .new.
    set_file = os.path.join(repo, BENCH_SET_FILE)
    if os.path.isfile(set_file):
        names = [os.path.basename(l.strip())[:-5] for l in open(set_file) if l.strip().endswith(".smt2")]
    else:
        names = [os.path.basename(f)[:-5] for f in glob.glob(os.path.join(bench_dir, "*.smt2"))
                 if ".new." not in os.path.basename(f)]
    names = sorted(set(names))
    missing = [n for n in names if not os.path.isfile(os.path.join(bench_dir, n + ".smt2"))]
    if missing:
        raise SystemExit("benchmark files missing in %s: %s" % (bench_dir, missing))

    # Guard: the files must not switch finite model finding on themselves,
    # otherwise the no-FMF configurations would silently run with it.
    with_fmf = [n for n in files_with_fmf(bench_dir) if n in names]
    if with_fmf:
        raise SystemExit("%s in %s contain (set-option :finite-model-find true); point --benchmarks-dir at the "
                         "no-FMF files, finite model finding is enabled per configuration with %s"
                         % (", ".join(with_fmf), bench_dir, FMF[0]))
    log("benchmarks in %s at %s (%d files): %s" % (bench_dir, head, len(names), ", ".join(names)))
    return dict(repo=repo, rev=head, bench_dir=bench_dir, names=names)


def benchmark_path(bench, name, config):
    return os.path.join(bench["bench_dir"], name + ".smt2")


# --------------------------------------------------------------------------
# Running cvc5
# --------------------------------------------------------------------------

def start_process(cvc5, path, opts, timeout_s, outfile):
    cmd = [cvc5, "--tlimit=%d" % int(timeout_s * 1000)] + list(opts) + [path]
    out = open(outfile, "w")
    out.write("$ " + " ".join(cmd) + "\n")
    out.flush()
    p = subprocess.Popen(cmd, stdout=out, stderr=subprocess.STDOUT, start_new_session=True)
    return p, out, cmd


def kill_process(p):
    for sig in (signal.SIGTERM, signal.SIGKILL):
        if p.poll() is not None:
            return
        try:
            os.killpg(os.getpgid(p.pid), sig)
        except ProcessLookupError:
            return
        try:
            p.wait(timeout=2)
            return
        except subprocess.TimeoutExpired:
            continue


def classify_output(outfile):
    """Skip the command line echoed as the first line of the output file."""
    try:
        lines = [l.strip() for l in open(outfile, errors="replace") if l.strip()]
    except OSError:
        return "error:no-output"
    lines = [l for l in lines if not l.startswith("$ ")]
    if not lines:
        return "error:empty"
    first = lines[0]
    if first in ("sat", "unsat", "unknown"):
        return first
    if first.startswith("cvc5 interrupted by timeout"):
        return "timeout"
    return "error:" + first[:60]


def run_single(cvc5, path, opts, timeout_s, outfile):
    """One run to completion (virtual mode)."""
    t0 = time.monotonic()
    p, out, cmd = start_process(cvc5, path, opts, timeout_s, outfile)
    try:
        p.wait(timeout=timeout_s + HARD_TIMEOUT_GRACE)
        result = None
    except subprocess.TimeoutExpired:
        kill_process(p)
        result = "timeout"
    t = time.monotonic() - t0
    out.close()
    if result is None:
        result = classify_output(outfile)
    return dict(result=result, time=round(t, 3), cmd=" ".join(cmd), out=outfile)


# --------------------------------------------------------------------------
# Virtual portfolio
# --------------------------------------------------------------------------

def run_virtual(cvc5, bench, args, outdir):
    os.makedirs(outdir, exist_ok=True)
    tasks = [(n, c) for n in bench["names"] for c in args.configs]
    runs = {}

    def one(task):
        n, c = task
        d = os.path.join(outdir, c)
        os.makedirs(d, exist_ok=True)
        r = run_single(cvc5, benchmark_path(bench, n, c), CONFIGS[c]["opts"], args.timeout,
                       os.path.join(d, n + ".out"))
        log("virtual  %-20s %-12s %-8s %8.2f s" % (n, c, r["result"], r["time"]))
        return task, r

    if args.jobs > 1:
        log("virtual portfolio: %d runs, %d at a time (times may suffer from contention)" % (len(tasks), args.jobs))
        with ThreadPoolExecutor(max_workers=args.jobs) as ex:
            for task, r in ex.map(one, tasks):
                runs[task] = r
    else:
        log("virtual portfolio: %d runs, strictly one at a time" % len(tasks))
        for task in tasks:
            runs[task] = one(task)[1]

    table = analyse_virtual(bench, args, runs)
    json.dump(dict(mode="virtual", timeout=args.timeout, jobs=args.jobs, cvc5=cvc5,
                   cvc5_version=cvc5_version(cvc5), benchmarks_rev=bench["rev"],
                   configs={c: CONFIGS[c] for c in args.configs},
                   runs={"%s|%s" % k: v for k, v in runs.items()}, table=table),
              open(os.path.join(outdir, "runs.json"), "w"), indent=1)
    md = virtual_markdown(bench, args, table)
    open(os.path.join(outdir, "summary.md"), "w").write(md)
    print("\n" + md)
    return table


def solved(result):
    return result in ("sat", "unsat")


def analyse_virtual(bench, args, runs):
    rows = []
    for n in bench["names"]:
        per = OrderedDict((c, runs[(n, c)]) for c in args.configs)
        answers = set(r["result"] for r in per.values() if solved(r["result"]))
        best_c, best_t, best_a = None, None, None
        for c, r in per.items():
            if solved(r["result"]) and (best_t is None or r["time"] < best_t):
                best_c, best_t, best_a = c, r["time"], r["result"]
        # cascade: configurations tried in order, each with the full limit
        cascade = 0.0
        cascade_c = None
        for c, r in per.items():
            cascade += r["time"]
            if solved(r["result"]):
                cascade_c = c
                break
        exp = EXPECTED.get(n) if not args.no_expected else None
        flags = []
        if len(answers) > 1:
            flags.append("DISAGREE")
        if exp and best_a and best_a != exp:
            flags.append("WRONG")
        rows.append(dict(benchmark=n, expected=exp, per_config={c: (r["result"], r["time"]) for c, r in per.items()},
                         vbs_config=best_c, vbs_time=best_t, vbs_answer=best_a,
                         cascade_time=round(cascade, 2) if cascade_c else None, cascade_config=cascade_c,
                         flags=flags))
    return rows


def fmt_cell(result, t):
    if solved(result):
        return "%s %.2f s" % (result, t)
    return result if not result.startswith("error") else result


def virtual_markdown(bench, args, table):
    cfgs = args.configs
    lines = ["# Virtual portfolio (virtual best solver), time limit %d s per run" % args.timeout, "",
             "cvc5: `%s`  " % cvc5_version(args.cvc5_binary),
             "benchmarks: relational-solver-benchmarks @ %s  " % bench["rev"][:9],
             "runs: one process at a time" if args.jobs == 1 else "runs: %d processes at a time" % args.jobs, "",
             "Per benchmark the VBS takes the fastest configuration that solved it (minimum time); "
             "the cascade column is the sum when the configurations are tried in the listed order instead.", "",
             "| benchmark | expected | " + " | ".join(cfgs) + " | VBS | VBS time | cascade | flags |",
             "|---|---|" + "---|" * len(cfgs) + "---|---|---|---|"]
    counts = {c: 0 for c in cfgs}
    vbs_count = 0
    for row in table:
        cells = []
        for c in cfgs:
            r, t = row["per_config"][c]
            if solved(r):
                counts[c] += 1
            cells.append(fmt_cell(r, t))
        if row["vbs_config"]:
            vbs_count += 1
        lines.append("| %s | %s | %s | %s | %s | %s | %s |" % (
            row["benchmark"], row["expected"] or "", " | ".join(cells),
            row["vbs_config"] or "unsolved",
            ("%.2f s" % row["vbs_time"]) if row["vbs_time"] is not None else "",
            ("%.2f s (%s)" % (row["cascade_time"], row["cascade_config"])) if row["cascade_time"] is not None else "",
            " ".join(row["flags"])))
    lines += ["", "Solved: " + ", ".join("%s %d" % (c, counts[c]) for c in cfgs) +
              "; virtual portfolio %d of %d." % (vbs_count, len(table))]
    wrong = [r["benchmark"] for r in table if "WRONG" in r["flags"] or "DISAGREE" in r["flags"]]
    lines.append("Wrong or disagreeing answers: %s." % (", ".join(wrong) if wrong else "none"))
    return "\n".join(lines) + "\n"


# --------------------------------------------------------------------------
# Real portfolio
# --------------------------------------------------------------------------

def run_real_one(cvc5, bench, name, args, outdir):
    """Start all configurations at once; first sat/unsat wins and kills the rest."""
    os.makedirs(outdir, exist_ok=True)
    ru0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    procs = OrderedDict()
    t0 = time.monotonic()
    for c in args.configs:
        outfile = os.path.join(outdir, c + ".out")
        p, out, cmd = start_process(cvc5, benchmark_path(bench, name, c), CONFIGS[c]["opts"], args.timeout, outfile)
        procs[c] = dict(p=p, out=out, outfile=outfile, cmd=" ".join(cmd), result=None, time=None)
    winner, winner_time, winner_answer = None, None, None
    hard_limit = args.timeout + HARD_TIMEOUT_GRACE
    while any(v["result"] is None for v in procs.values()):
        now = time.monotonic() - t0
        for c, v in procs.items():
            if v["result"] is not None:
                continue
            rc = v["p"].poll()
            if rc is not None:
                v["out"].close()
                v["time"] = round(now, 3)
                v["result"] = classify_output(v["outfile"])
                if solved(v["result"]) and winner is None:
                    winner, winner_time, winner_answer = c, v["time"], v["result"]
                    for c2, v2 in procs.items():
                        if v2["result"] is None:
                            kill_process(v2["p"])
                            v2["out"].close()
                            v2["time"] = round(time.monotonic() - t0, 3)
                            v2["result"] = "killed"
            elif now > hard_limit:
                kill_process(v["p"])
                v["out"].close()
                v["time"] = round(now, 3)
                v["result"] = "timeout"
        time.sleep(POLL_INTERVAL)
    wall = round(time.monotonic() - t0, 3)
    ru1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = round((ru1.ru_utime - ru0.ru_utime) + (ru1.ru_stime - ru0.ru_stime), 2)
    exp = EXPECTED.get(name) if not args.no_expected else None
    flags = []
    if winner_answer and exp and winner_answer != exp:
        flags.append("WRONG")
    others = set(v["result"] for v in procs.values() if solved(v["result"]))
    if len(others) > 1:
        flags.append("DISAGREE")
    row = dict(benchmark=name, expected=exp, winner=winner, answer=winner_answer,
               time=winner_time, wall=wall, cpu=cpu, flags=flags,
               per_config={c: dict(result=v["result"], time=v["time"], cmd=v["cmd"]) for c, v in procs.items()})
    log("real     %-20s %-8s %-12s %8.2f s wall, %7.2f s cpu" % (
        name, winner_answer or "unsolved", winner or "-", wall, cpu))
    return row


def run_real(cvc5, bench, args, outdir):
    os.makedirs(outdir, exist_ok=True)
    log("real portfolio: %d benchmarks, %d configurations in parallel each" % (len(bench["names"]), len(args.configs)))
    table = [run_real_one(cvc5, bench, n, args, os.path.join(outdir, n)) for n in bench["names"]]
    json.dump(dict(mode="real", timeout=args.timeout, cvc5=cvc5, cvc5_version=cvc5_version(cvc5),
                   benchmarks_rev=bench["rev"], configs={c: CONFIGS[c] for c in args.configs}, table=table),
              open(os.path.join(outdir, "runs.json"), "w"), indent=1)
    md = real_markdown(bench, args, table)
    open(os.path.join(outdir, "summary.md"), "w").write(md)
    print("\n" + md)
    return table


def real_markdown(bench, args, table):
    cfgs = args.configs
    lines = ["# Real portfolio (%d configurations in parallel, first sat/unsat wins), time limit %d s" % (len(cfgs), args.timeout), "",
             "cvc5: `%s`  " % cvc5_version(args.cvc5_binary),
             "benchmarks: relational-solver-benchmarks @ %s" % bench["rev"][:9], "",
             "| benchmark | expected | answer | winner | time | CPU (all processes) | " + " | ".join(cfgs) + " | flags |",
             "|---|---|---|---|---|---|" + "---|" * len(cfgs) + "---|"]
    n_solved = 0
    for row in table:
        if row["winner"]:
            n_solved += 1
        cells = []
        for c in cfgs:
            pc = row["per_config"][c]
            cells.append("%s %.2f s" % (pc["result"], pc["time"]) if pc["time"] is not None else pc["result"])
        lines.append("| %s | %s | %s | %s | %s | %.2f s | %s | %s |" % (
            row["benchmark"], row["expected"] or "", row["answer"] or "unsolved", row["winner"] or "-",
            ("%.2f s" % row["time"]) if row["time"] is not None else ("timeout %.0f s" % row["wall"]),
            row["cpu"], " | ".join(cells), " ".join(row["flags"])))
    wrong = [r["benchmark"] for r in table if r["flags"]]
    lines += ["", "Solved: %d of %d. Wrong or disagreeing answers: %s." % (
        n_solved, len(table), ", ".join(wrong) if wrong else "none"),
        "Wins: " + ", ".join("%s %d" % (c, sum(1 for r in table if r["winner"] == c)) for c in cfgs) + "."]
    return "\n".join(lines) + "\n"


def comparison_markdown(virtual, real, args):
    lines = ["# Virtual versus real portfolio (time limit %d s)" % args.timeout, "",
             "| benchmark | VBS config | VBS time | real winner | real time | real / VBS |",
             "|---|---|---|---|---|---|"]
    rv = {r["benchmark"]: r for r in real}
    for v in virtual:
        r = rv.get(v["benchmark"])
        ratio = ""
        if v["vbs_time"] and r and r["time"]:
            ratio = "%.2f" % (r["time"] / v["vbs_time"])
        lines.append("| %s | %s | %s | %s | %s | %s |" % (
            v["benchmark"], v["vbs_config"] or "unsolved",
            ("%.2f s" % v["vbs_time"]) if v["vbs_time"] is not None else "",
            (r["winner"] or "unsolved") if r else "", ("%.2f s" % r["time"]) if r and r["time"] is not None else "",
            ratio))
    nv = sum(1 for v in virtual if v["vbs_config"])
    nr = sum(1 for r in real if r["winner"])
    same = sum(1 for v in virtual if v["vbs_config"] and rv.get(v["benchmark"], {}).get("winner") == v["vbs_config"])
    lines += ["", "Solved: virtual %d, real %d. Same winning configuration in %d of %d solved benchmarks." % (nv, nr, same, nv),
              "The real time includes process start-up and the contention of %d concurrent processes; "
              "the VBS is its lower bound." % len(args.configs)]
    return "\n".join(lines) + "\n"


# --------------------------------------------------------------------------
# cvc5's own portfolio mode
# --------------------------------------------------------------------------

def check_cvc5_portfolio(cvc5, bench, args):
    """Show what cvc5's built-in --use-portfolio would do on these benchmarks."""
    print("cvc5's built-in portfolio (src/main/portfolio_driver.cpp):")
    print("  --use-portfolio        run a fixed list of option sets chosen by the (set-logic ...) of the input")
    print("  --portfolio-jobs=N     run up to N of them concurrently (fork); default 1 = one after another")
    print("  --portfolio-dry-run    only print the option sets")
    print("  -o portfolio           print each option set as it is tried")
    print("The option sets are hard-coded per logic and cannot be given on the command line.\n")
    name = bench["names"][0]
    path = os.path.join(bench["bench_dir"], name + ".smt2")
    for extra in (["--use-portfolio", "--portfolio-dry-run", "-o", "portfolio"],):
        cmd = [cvc5] + extra + [path]
        print("$ " + " ".join(cmd))
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
        print((p.stdout + p.stderr).strip() or "(no output: a single, default strategy)")
    logic = ""
    for l in open(path):
        if l.startswith("(set-logic"):
            logic = l.strip()
            break
    print("\nThe benchmarks use %s; for this logic the driver falls into its final `else` branch, "
          "which adds exactly one strategy with no options. So cvc5's portfolio mode runs the\n"
          "default configuration once and cannot run the configurations of this study." % logic)


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------

def parse_args(argv):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--workdir", default="portfolio-work", help="where cvc5 and the benchmarks are cloned/built (default: portfolio-work)")
    ap.add_argument("--results", default=None, help="results directory (default: <workdir>/results/<tag>)")
    ap.add_argument("--tag", default=None, help="name of this run (default: date and time)")
    ap.add_argument("--mode", choices=["setup", "virtual", "real", "both", "cvc5-portfolio"], default="both")
    ap.add_argument("--timeout", type=float, default=300.0, help="time limit per cvc5 process in seconds (default 300)")
    ap.add_argument("--jobs", type=int, default=1, help="virtual mode: runs executed concurrently (default 1 = strictly sequential)")
    ap.add_argument("--benchmarks", nargs="+", default=None, help="restrict to these benchmark names")
    ap.add_argument("--configs", nargs="+", default=None, help="configurations to use (names from the built-in table or from --configs-file)")
    ap.add_argument("--configs-file", default=None,
                    help="JSON file {name: {\"opts\": [...], \"desc\": str}} replacing the built-in configurations "
                         "(add --finite-model-find to opts for finite model finding)")
    ap.add_argument("--no-expected", action="store_true", help="do not compare answers with the hand-verified expectations")
    ap.add_argument("--cvc5", default=None, help="use this cvc5 binary (or the directory containing it) instead of cloning and building")
    ap.add_argument("--cvc5-repo", default=CVC5_REPO)
    ap.add_argument("--cvc5-branch", default=CVC5_BRANCH)
    ap.add_argument("--cvc5-rev", default=CVC5_REV, help="commit to build (default: the code of rachelcleaveland/cvc5#9; 'HEAD' for the branch tip)")
    ap.add_argument("--rebuild", action="store_true", help="rebuild cvc5 even if a build exists")
    ap.add_argument("--build-jobs", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--benchmarks-dir", "--bench-dir", dest="benchmarks_dir", default=None,
                    help="use the benchmarks in this local directory (the repository root or the directory of no-FMF "
                         ".smt2 files itself) instead of cloning; no git needed")
    ap.add_argument("--nofmf-dir", default=None, help=argparse.SUPPRESS)  # removed; rejected in main
    ap.add_argument("--benchmarks-repo", default=BENCH_REPO, help="git URL to clone when --benchmarks-dir is not given")
    ap.add_argument("--benchmarks-rev", default=BENCH_REV, help="commit of the benchmark repository ('HEAD' for the tip)")
    return ap.parse_args(argv)


def main(argv):
    args = parse_args(argv)
    if args.configs_file:
        loaded = json.load(open(args.configs_file), object_pairs_hook=OrderedDict)
        CONFIGS.clear()
        for name, c in loaded.items():
            if c.get("nofmf") is not None:
                raise SystemExit("configuration %s: 'nofmf' is no longer supported; all configurations run the "
                                 "no-FMF files, add %s to opts instead" % (name, FMF[0]))
            CONFIGS[name] = dict(opts=list(c.get("opts", [])), desc=c.get("desc", ""))
    if args.configs is None:
        args.configs = list(CONFIGS)
    unknown = [c for c in args.configs if c not in CONFIGS]
    if unknown:
        raise SystemExit("unknown configurations: %s (known: %s)" % (unknown, list(CONFIGS)))
    if args.nofmf_dir:
        raise SystemExit("--nofmf-dir no longer exists: give the directory of no-FMF files as --benchmarks-dir, "
                         "finite model finding is enabled per configuration with %s" % FMF[0])
    args.workdir = os.path.abspath(args.workdir)
    os.makedirs(args.workdir, exist_ok=True)
    tag = args.tag or datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
    results = os.path.abspath(args.results) if args.results else os.path.join(args.workdir, "results", tag)

    cvc5 = ensure_cvc5(args)
    args.cvc5_binary = cvc5
    log("cvc5 version: %s" % cvc5_version(cvc5))
    check_options(cvc5, args.configs)
    bench = ensure_benchmarks(args)
    if args.benchmarks:
        unknown = [b for b in args.benchmarks if b not in bench["names"]]
        if unknown:
            raise SystemExit("unknown benchmarks: %s" % unknown)
        bench["names"] = [n for n in bench["names"] if n in args.benchmarks]
    if args.mode == "setup":
        log("setup done")
        return
    if args.mode == "cvc5-portfolio":
        check_cvc5_portfolio(cvc5, bench, args)
        return

    os.makedirs(results, exist_ok=True)
    log("results go to %s" % results)
    virtual = real = None
    if args.mode in ("real", "both"):
        real = run_real(cvc5, bench, args, os.path.join(results, "real"))
    if args.mode in ("virtual", "both"):
        virtual = run_virtual(cvc5, bench, args, os.path.join(results, "virtual"))
    if virtual is not None and real is not None:
        md = comparison_markdown(virtual, real, args)
        open(os.path.join(results, "comparison.md"), "w").write(md)
        print("\n" + md)
    log("done; results in %s" % results)


if __name__ == "__main__":
    main(sys.argv[1:])
