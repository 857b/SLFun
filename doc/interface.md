Interface
=========================================

### Vprops

A vprop `v` of selector type `sel_t` has type `VProp.p sel_t`, that is, it is a
separation logic predicate `sel_t -> SLprop.t`.
The type `Vprop.t` uses a sigma type to store the selector type, it is used to
combine several vprops of different selector types:

```coq
(* namespace: Vprop *)
Record t := mk {
  ty : Type@{sel};
  sl : p ty;
}.
```

Given a selector `s : sel_t`, we can instantiate `v` to obtain a separation
logic proposition. Instead of using a direct application `v s`, we use a sigma
to separate the vprop from the selector and avoid unwanted reductions.
An instantiated vprop has type:

```coq
(* namespace: CTX *)
Definition atom := {v : Vprop.t & Vprop.ty v}.
```

We use the following notations:
- `v ~>` is the `Vprop.t` associated to `v`
- `v ~> s` is the `CTX.atom` obtained by instantiating `v` with `s`

### Specifications

A specification (for a function or a lemma) is declared using the following
notation (from [VProg.Core)](../VProg/Core.v):

```coq
SPEC (args : args_ty) & (gargs : garg_ty)
'sel0 prs_ctx pre_ctx req & REQ
'(res : res_ty) & (gres : gres_ty) sel1 post_ctx ens
```

where:
- `(args : args_ty)` is a pattern for the arguments of the function,
  for instance `((p0, n) : ptr * nat)`
- `(gargs : garg_ty)` is an optional pattern for the ghost arguments
- `sel0` binds the input selectors. Each input selector must occur exactly once
  as the selector of a vprop of [prs_ctx] or [pre_ctx].
  It is a tuple of variables, for instance: `tt` (no selectors),
  `sel` (a single selector), `(sel0, sel1)` (two selectors).
- `prs_ctx` is the preserved context, that is a list of [atom] that are present
  in the context at the beginning of the function and that must be restored
  (with the same selector) at its end.
- `pre_ctx` is the precondition context, [atom] present only at the beginning
  of the function.
- `req` (requires) is a proposition that expresses a pure precondition on the
  arguments and on the input selectors.
  It can optionally be bound with `& REQ` to be used in `post_ctx` and `ens`.
- `(res : res_ty)` is a name that binds the returned value.
- `(gres : gres_ty)` is an optional name for the ghost returned value.
- `sel1` binds the output selectors, using a tuple like `sel0`.
- `post_ctx` is the postcondition context.
- `ens` (ensures) is a proposition expressing a postcondition.
  It can depend on all the previously bound variables.

There are the following restrictions, that can trigger an error either at the
declaration or at the use:
- Each input selectors mist occur exactly once as the selector of a vprop of
  `prs_ctx` or `pre_ctx`.
- All selectors of `prs_ctx` and `pre_ctx` must be variables from `sel0`.
- One cannot pattern match on the returned value (or on the ghost one), if it
  is a record, one must use projections in `post_ctx`.
- The vprops of `post_ctx` must be independents of `sel1`, but their selectors
  can and can also be arbitrary expressions not necessarily variables of `sel1`.
- More generally, the vprops of `prs_ctx`, `pre_ctx` and `post_ctx` should not
  depend on the selectors.

The following command will declare a specification `spec_name`:

```coq
Definition spec_name : FDecl SPEC...
Proof. Derived. Defined.
```

This command will process the specification so that it can be used by the
framework.
`spec_name` store the processed version of the specification (which is proved
equivalent to the input one).

### Lemmas

A lemma is declared using:

```coq
Derive lem_name_spec SuchThat (
  VLem SPEC...
  lem_name_spec) As lem_name.
```

The proof begins with the `init_lemma args sel0 REQ` which processes the
specification (recording the processed version in `lem_name`) like `FDecl`
does.
It leaves as goal the underlying separation logic entailment.
It uses its arguments to introduce the lemma's arguments, input selectors and
requires clause. Those arguments can be introduction patterns.
The user then need to solves this entailment and close the proof with `Qed`.

#### Automatic introduction/elimination rules

The proofs obligation about the shape of the memory that the tactics solves
reduces to finding a transformation between two contexts (list of atoms).
For instance, when calling a function with precondition `[vptr p0 ~>]` in a
context `[vptr p1 ~> sel1; vptr p0 ~> sel0]`, we need to find a transformation:

```coq
[vptr p1 ~> sel1; vptr p0 ~> sel0]  |->  vptr p0 ~> ?sel :: ?frame
```

where a transformation (noted `|->` here) can be seen in first approximation as
an entailment.
In particular, we can change the order of the atoms and the above example can be
solved by choosing `?sel := sel0` and `?frame := vptr p1 ~> sel1`.
But our solver is also able to use some basic introduction and elimination rules
to avoid needing to call some lemmas in the program implementations.
An introduction (resp. elimination) rule allows to replace an atom that appears
in the target (resp. source) context of the transformation by a list of other
atoms.
For instance, the list cell `lcell p` described in the
[example program](./example_SLList.md) can be replaced with two `vptr` (one for
each field).
Custom rules can be added to the `CtxTrfDB`.

The modules `VRecord` and `VGroup` in [Vprop](../VProg/Vprop.v) defines vprops
already equipped with introduction and elimination rules.
`VRecord` allows the definition of C-like structures such as `lcell`:

```coq
Lemma lcell_p (p : ptr):
  VRecord.p lcell_t [vptr (p_data p) ~>; vptr (p_next p) ~>]
    (fun v => (v_data v, v_next v))
    (fun dt nx => mk_lcell dt nx).
Proof.
  constructor; cbn; reflexivity.
Qed.

Definition lcell (p : ptr) : Vprop.p lcell_t := VRecord.v (lcell_p p).
```

In order for the solver to apply the rules defined for `VRecord` to `lcell`,
one must add an unfolding rule to `CtxTrfDB`:

```coq
Definition lcell_unfold p sl:
  CTX.Trf.Tac.unfold_rule (lcell p ~> sl) (VRecord.v (lcell_p p) ~> sl).
Proof.
  reflexivity.
Qed.

Local Hint Resolve lcell_unfold | 1 : CtxTrfDB.
```

Also note that `VRecord.Tactics` must be imported.

### Functions

In order to be able to compose programs from functions defined in different
modules, we parametrize their definition by a context containing the declaration
of the final program.
The context is declared as a variable in the section containing the
implementations:

```coq
Variable CT : ConcreteProg.context.
```

Given a function specification `fun_spec : FDecl SPEC...`, `fun_spec CT`
represents the hypothesis that a function with specification `fun_spec` is
declared in the context.
Those hypotheses should also be declared as variables:

```coq
Variable fun_name : fun_spec CT.
```

Those variables can then be used in implementations to call the function:
`fun_name arg` (or `fun_name arg ghost_arg` if there are ghost arguments).

The implementation of a function as a vprog is defined with:

```coq
Definition fun_impl : FImpl fun_name := fun arg ghost_arg =>
  body.
```

The correctness of such implementation is expressed by a lemma:

```coq
Lemma fun_correct : FCorrect fun_impl.
```

The first step of this proof is the translation of the proof obligations into a
functional program using `build_fun_spec`.
We can then use tactics defined in [FunProg](../FunProg.v) to solve the goal.
On can also directly call the tactic `solve_by_wlp`, which call
`build_fun_spec`, generate a verification condition using a weakest precondition
and decompose it using a tactic similar to `intuition`.

#### Fragments

Fragments are pieces of code that can be defined using an interface similar to
functions but which are inlined in the final program. Hence they do not generate
a function in the program (so they cannot be recursive).

Given a specification `frag_spec : FDecl SPEC...`, a fragment implementation can
defined with with a vprog using:

```coq
Definition frag_impl : FragImpl frag_spec CT := fun arg ghost_arg =>
  body.
```

and proved correct using the same tactics as for the functions:

```coq
Lemma frag : FragCorrect frag_impl.
Proof.
  solve_by_wlp. (* for instance *)
Qed.
```

They can then be called from functions or other fragments using
`frag arg ghost_arg`.

The main use of fragments is to build libraries parametrized by the objects they
uses.
For instance [Lib.DLList](../Lib/DLList.v) defines doubly linked list using an
abstract vprop to represent the list cells. It is parametrized by a set
`Param.impl` of fragments that implements the reading and writing operations on
the `prev` and `next` fields.

### Program composition

A closed concrete program can be built from a list of functions using the
following declarations:

```coq
Definition entries : list ConcreteProg.context_entry :=
  (* list of program entries *).

Derive prog SuchThat (ConcreteProg.of_entries entries prog) As prog_correct.
Proof. Derived. Qed.
```

The list `entry` must contains all the functions needed to obtain a closed
program. In particular it must include the functions defined in the libraries it
uses. To this end, each library should declare the list of functions it defines
(for instance `Malloc.entries`).
Currently the only possible entry type is:

```coq
f_entry fun_spec fun_correct
```

where `fun_spec` is the specification of the function and `fun_correct` is the
proof of the correctness of the chosen implementation.

`ConcreteProg.of_entries` also has an optional argument `aux` which allows to
provide some auxiliary definitions needed by some functions.
For instance in [Test.DLList](../Test/DLList.v) one must provide the
implementations needed by the parametrized doubly linked list library:

```coq
Check iP : forall CT, DL.Param.impl vP CT.

Definition entries := [
  f_entry Main_spec     Main_correct
] ++ Malloc.entries ++ DL.entries vP.

Derive prog SuchThat (ConcreteProg.of_entries entries (aux := [existT _ _ iP]) prog)
  As prog_correct.
Proof. Derived. Qed.
```
