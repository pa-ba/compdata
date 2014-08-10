Compositional Data Types
========================

This library implements the ideas of
[*Data types a la carte*](http://dx.doi.org/10.1017/S0956796808006758)
(Journal of Functional Programming, 18(4):423-436, 2008) as outlined
in the paper
[*Compositional data types*](http://dx.doi.org/10.1145/2036918.2036930)
(Workshop on Generic Programming, 83-94, 2011). The purpose of this
library is to allow the programmer to construct data types -- as well
as the functions defined on them -- in a modular fashion. The
underlying idea is to separate the signature of a data type from the
fixed point construction that produces its recursive
structure. Signatures can then be composed and decomposed freely.


Building on that foundation, this library provides additional
extensions and (run-time) optimisations which make compositional data
types usable for practical implementations. In particular, it provides
an excellent framework for manipulating and analysing abstract syntax
trees in a type-safe manner. Thus, it is perfectly suited for
programming language implementations, especially, in an environment
consisting of a family of tightly interwoven *domain-specific
languages*.

In concrete terms, this library provides the following
features:

* Compositional data types in the style of Wouter Swierstra's
   Functional Pearl *Data types a la carte*. The implementation of
   signature subsumption is based on the paper
   [*Composing and Decomposing Data Types*](http://www.pa-ba.net/pubs/entries/bahr14wgp.html)
   (Workshop on Generic Programming, 2014, to appear), which makes
   signature composition more flexible.
* Modular definition of functions on compositional data types through
   catamorphisms and anamorphisms as well as more structured recursion
   schemes such as primitive recursion and co-recursion, and
   course-of-value iteration and co-iteration.
* Support for monadic computations via monadic variants of all
   recursion schemes.
*  Support of a succinct programming style over compositional data types
   via generic programming combinators that allow various forms of
   generic transformations and generic queries.
*  Generalisation of compositional data types (terms) to
   compositional data types "with holes" (contexts). This allows
   flexible reuse of a wide variety of catamorphisms (called
   *term homomorphisms*) as well as an efficient composition of them.
*  Operations on signatures, for example, to add and remove
   annotations of abstract syntax trees. This includes combinators to
   propagate annotations fully automatically through certain
   term homomorphisms.
*  Optimisation of the implementation of recursion schemes. This
   includes *short-cut fusion* style optimisation rules which yield a
   performance boost of up to factor six.
*  Automatic derivation of instances of all relevant type classes for
   using compositional data types via *Template Haskell*. This includes
   instances of `Prelude.Eq`, `Prelude.Ord` and `Prelude.Show` that are
   derived via instances for functorial variants of them. Additionally,
   also *smart constructors*, which allow to easily construct inhabitants
   of compositional data types, are automatically generated.
*  *Mutually recursive data types* and
   *generalised algebraic data types (GADTs)*. All of the above is also lifted
   to families of mutually recursive data types and (more generally) GADTs.
   This extension resides in the module *Data.Comp.Multi*.
* Advanced recursion schemes derived from tree automata. These
  recursion schemes allow for a higher degree of modularity and make
  it possible to apply fusion. See
  [*Modular Tree Automata*](http://dx.doi.org/10.1007/978-3-642-31113-0_14)
  (Mathematics of Program Construction, 263-299, 2012) and
  [*Programming Macro Tree Transducers*](http://dx.doi.org/10.1145/2502488.2502489) (Workshop on Generic
  Programming, 61-72, 2013).

Examples of using (generalised) compositional data types are bundled
with the package in the folder `examples`.

Previous versions of this library contained a parametric variant of
compositional data types. This former part of the library has been
moved to a separate package:
[`compdata-param`](https://hackage.haskell.org/package/compdata-param)
