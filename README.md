SLFun: Separation Logic Functionalization
=========================================

SLFun is a toy framework to define imperative programs proven correct using
separation logic in the [Coq](https://coq.inria.fr/) proof assistant.
It separates the proof obligations about the shape of the memory from the ones
about the contents of the memory objects.
After the resolution of the formers, the later are presented as a functional
program whose correctness can be proven using standard methods.
It is inspired by the [Steel](https://github.com/FStarLang/steel) framework of
[F\*](http://www.fstar-lang.org/) and borrows some of its concepts.

See [.versions](./.versions) for the currently used Coq version.
At the root of the repository, `make` should verify the whole project,
including examples.
The `.v` files can then be visited interactively.

See the [doc](./doc) directory for a description of the module and
[Test/SLList.v](./Test/SLList.v) for an example of a program.
