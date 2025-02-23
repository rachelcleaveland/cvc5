C++ API Documentation
=====================

The C++ API is the primary interface for cvc5 and exposes the full functionality of cvc5.
The :doc:`quickstart guide <quickstart>` gives a short introduction, while the following class hierarchy of the ``cvc5::api`` namespace provides more details on the individual classes.
For most applications, the :cpp:class:`Solver <cvc5::api::Solver>` class is the main entry point to cvc5.


.. container:: hide-toctree

  .. toctree::
    :maxdepth: 0

    quickstart
    exceptions
    datatype
    datatypeconstructor
    datatypeconstructordecl
    datatypedecl
    datatypeselector
    grammar
    kind
    op
    optioninfo
    result
    roundingmode
    solver
    sort
    statistics
    term


Class hierarchy
^^^^^^^^^^^^^^^

``namespace cvc5::api {``
  
  * class :cpp:class:`CVC5ApiException <cvc5::api::CVC5ApiException>`
  * class :cpp:class:`CVC5ApiRecoverableException <cvc5::api::CVC5ApiRecoverableException>`
  * class :ref:`api/cpp/datatype:datatype`

    * class :cpp:class:`const_iterator <cvc5::api::Datatype::const_iterator>`

  * class :ref:`api/cpp/datatypeconstructor:datatypeconstructor`

    * class :cpp:class:`const_iterator <cvc5::api::DatatypeConstructor::const_iterator>`

  * class :ref:`api/cpp/datatypeconstructordecl:datatypeconstructordecl`
  * class :ref:`api/cpp/datatypedecl:datatypedecl`
  * class :ref:`api/cpp/datatypeselector:datatypeselector`
  * class :ref:`api/cpp/grammar:grammar`
  * class :ref:`api/cpp/kind:kind`
  * class :ref:`api/cpp/op:op`
  * class :ref:`api/cpp/optioninfo:optioninfo`
  * class :ref:`api/cpp/result:result`

    * enum :cpp:enum:`UnknownExplanation <cvc5::api::Result::UnknownExplanation>`

  * class :ref:`api/cpp/roundingmode:roundingmode`
  * class :ref:`api/cpp/solver:solver`
  * class :ref:`api/cpp/sort:sort`
  * class :cpp:class:`Stat <cvc5::api::Stat>`
  * class :cpp:class:`Statistics <cvc5::api::Statistics>`
  * class :ref:`api/cpp/term:term`

    * class :cpp:class:`const_iterator <cvc5::api::Term::const_iterator>`

``}``