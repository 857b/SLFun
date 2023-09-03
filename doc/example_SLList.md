Program example: Singly Linked Lists
=========================================

This file is a short walk-through of the module [../Test/SLList.v](Test.SLList),
which defines some functions that use singly linked lists.
It illustrates how programs can be defined and proven correct in our framework.

### Definition of the vprops

Since the functions use singly linked lists, we must start by defining a vprops
that represent them.

Our lists are chains of list cells, with the following C-like signature:

```c
struct lcell {
  memdata data;
  struct lcell *next;
};
```

We first define a vprop to represent such list cell. An `lcell p` represents
a cell at address `p`. The content of the cell is described by the following
record:

```coq
Record lcell_t := mk_lcell {
  v_data : memdata;
  v_next : ptr;
}.
```

`lcell p` is a `Vprop.p lcell_t`, that is, a separation logic predicate `lcell_t
-> SLprop.t`.
Hence, given `sl : lcell_t` (called a selector), the application `lcell p sl` is
a separation logic proposition. For technical reasons, this application is often
represented as `lcell p ~> sl` instead of a direct application.

```coq
Check lcell : ptr -> Vprop.p lcell_t.
```

We skip its definition here but it corresponds to a points to assertion:

```coq
lcell p := fun c => p ↦ sl
```

Now that we have defined list cells, we can define list segments, again as a
vprop.
An `lseg l_entry l_next` represents a list segment whose first cell is at
address `l_entry` and such that the `next` pointer of the last cell points to
`l_next`.
The selector of a list segment is the (functional) list of the addresses of its
cells with the content of their `data` field.

```coq
Definition lseg_t := list (ptr * memdata).
```

List segments are defined as separation logic assertions, by induction on the
selector:

```coq
Definition lseg_entry (l : lseg_t) (sg_next : ptr) : ptr :=
  match l with
  | nil         => sg_next
  | (p, _) :: _ => p
  end.

Fixpoint lseg_sl (l : lseg_t) (sg_next : ptr) : SLprop.t :=
  match l with
  | nil          => SLprop.emp
  | (p, d) :: cs => lcell p (mk_lcell d (lseg_entry cs sg_next)) ** lseg_sl cs sg_next
  end.

Definition lseg (entry next : ptr) (v : lseg_t) : SLprop.t :=
  SLprop.pure (lseg_entry v next = entry) **
  lseg_sl v next.
```

Finally, we define a linked list as a null-terminated list segment.
Since `llist p` is simply an alias for `lseg p NULL`, we will be able to use
functions defined on `lseg` to handle `llist`.

```coq
Definition llist (p : ptr) : Vprop.p lseg_t :=
  lseg p NULL.
```

### Lemmas

Our implementations will rely on some properties of linked lists.
We need to state those properties as lemmas that will be called at the right
place in the implementations.
Consider for instance the `intro_lseg_cons` lemma, which allow adding a cell at
the beginning of a list.
Its specification is described by:

```coq
Derive intro_lseg_cons_spec SuchThat (
  VLem SPEC ((p0, p1, pn) : ptr * ptr * ptr)
  '(hd, tl) [] [lcell p0 ~> hd; lseg p1 pn ~> tl] (v_next hd = p1)
  '(_ : unit) tt [lseg p0 pn ~> ((p0, v_data hd) :: tl)] True
  intro_lseg_cons_spec) As intro_lseg_cons.
```

This lemmas takes three pointer arguments `p0` (the address of the added cell),
`p1` (the entry of the list) and `pn` (the next of the list).
Intuitively, the specification can be seen as:
- A pre-condition `[lcell p0 ~> hd; lseg p1 pn ~> tl] (v_next hd = p1)`.
  This precondition states that this lemma must be called in a context that
  contains a `lcell p0` and a `lseg p1 pn` with some selectors `hd` and `tl` and
  such that `v_next hd = p1`.
- A post-condition `[lseg p0 pn ~> ((p0, v_data hd) :: tl)] True`.
  This post-conditions states that after a call to this lemma, the vprops listed
  in the preconditions are replaced by a `lseg p0 pn` with selector
  `(p0, v_data hd) :: tl`.
  The final clause (`True` here) could be used to describe pure facts that holds
  after the call.
Note that we can extract from this specification the parts about the shape of
the memory as lists of vprops (without selectors),
here `[lcell p0 ~>; lseg p1 pn ~>]` and `[lseg p0 pn ~>]`.
When verifying implementations, this will allow us to solve the obligations
about the shape of the memory without taking into account (in a first step) its
content (that is the value of the selectors).

Lemmas unfolds to entailment (`SLprop.imp` in our notations) between
propositions in separation logic:

```coq
Proof.
  init_lemma ((p0, p1), pn) ([], tl) <-.
  (*
    SLprop.imp
      (lcell p0 {| v_data := v_data0; v_next := v_next0 |} ** lseg v_next0 pn tl)
      (lseg p0 pn ((p0, v_data0) :: tl))
   *)
  unfold lseg; SL.normalize.
  Intro ->.
  Apply; reflexivity.
Qed.
```

### Implementations

Once we have proved the necessary lemmas, we can defined and prove correct our
functions.
We will describe here the `Length` function.

We start by defining its specification, using the same format as for lemmas:

```coq
Definition Length_spec : FDecl SPEC
  (p : ptr)
  'l [llist p ~> l] [] True
  '(n : nat) tt [] (n = length l).
Proof. Derived. Defined.
```

Here, `llist p` appears in the list of preserved vprops (the list of vprops of
the precondition is empty). This clause is used to declare vprops that are
unchanged (including their selector value) by the function. It is
semantically equivalent to putting `llist p ~> l` both in the pre-condition and
in the post-condition. But the preserved clause is shorter and better handled.

The following declaration assumes that the function is declared in the program,
it will be used for calls (including recursive ones):

```coq
Variable Length : Length_spec CT.
```

We then define a possible implementation of the length function:

```coq
Definition Length_impl : FImpl Length := fun p0 =>
  (* [llist p0~>] *)
  if Mem.ptr_eq p0 NULL
  then
    (* [llist p0~>] *)
    gLem (lseg_null_nil p0 NULL) tt;;
    (* [llist p0~>] *)
    Ret 0
  else
    (* [llist p0~>] *)
    'g_p1 <- gLem elim_llist_nnull p0;
    (* [lcell p0~>; llist g_p1~>] *)
    'p1 <- Read (p_next p0);
    (* [lcell p0~>; llist g_p1~>] *)
    gRewrite g_p1 p1;;
    (* [lcell p0~>; llist p1~>] *)
    'n  <- Length p1;
    (* [lcell p0~>; llist p1~>] *)
    gLem intro_lseg_cons (p0, p1, NULL);;
    (* [llist p0~>] *)
    Ret (S n).
```

At each point of the program, we can define a context which contains the vprops
available at each point.
It is commented on this example but it normally remains implicit.
The implementation contains some ghost calls (`gLem` and `gRewrite`) that can
change the context or derive some properties needed to prove the correctness of
the program. For instance `gLem (lseg_null_nil p0 NULL) tt` allows us to prove
that the selector of `llist p0` is `nil` from the fact that `p0` is null.

We then prove that this implementation is correct with respect to the `Length`
specification:

```coq
Lemma Length_correct : FCorrect Length_impl.
```

We start by calling the `build_fun_spec` tactics.
This tactics solves the obligation about the shape of the memory by
inferring the context of vprops available at each point.
It will encode the remaining obligations as a functional program.
Here is a (manually) simplified version of this functional representation:

```coq
fun (p0 : ptr) (sel0 : lseg_t) =>
  if Mem.ptr_eq p0 NULL
  then
    (* lseg_null_nil *)
    call (req : p0 = NULL) (ens : sel0 = []);
    return (|0, sel0|)
  else
    (* elim_llist_nnull *)
    let (p1 : ptr) (dt : memdata) (tl : lseg_t) <- 
      call (req : p0 <> NULL)
           (ens (_ : ptr) (dt : memdata) (tl : lseg_t) : 
                sel0 = (p0, dt) :: tl);
    (* recursive call to Length *)
    let (len : nat) <- 
      call (ens (len : nat) : len = length tl);
    return (|S len, (p0, dt) :: tl|)
```

This representation involves the selectors of the vprops (which were implicit in
the implementation).

Once we have this representation, we can finish the proof by proving that it
matches the specification of `Length`.
For now, the only tool available is the generation of a verification condition
using a weakest precondition:

```coq
Proof.
  (* Build a functional specification for the function. *)
  build_fun_spec.
  (* Build a WLP from the functional specification. *)
  FunProg.by_wlp.
  (* Tactic to solve a WLP *)
  FunProg.solve_wlp; auto.
Qed.
```

### Program

After defining the functions we are interested in, we can compose them to obtain
a closed program.
We start by gathering the specification, implementation and correctness proof of
the functions we want to include:

```coq
Definition entries := [
  f_entry Main_spec     Main_correct;
  f_entry Length_spec   Length_loop_correct;
  f_entry Rev_spec      Rev_correct;
  f_entry Seg_Next_spec Seg_Next_correct
] ++ Malloc.entries.
```

Note that we import the functions needed by a toy `Malloc` module since our
`Main` function uses it.

We then call a tactic to build a program from those entries:

```coq
Derive prog SuchThat (ConcreteProg.of_entries entries prog) As prog_correct.
Proof. Derived. Qed.
```

The proven correctness lemma implies for instance the safety of our `Main`
function, in a small-step semantics defined on concrete programs:

```coq
Lemma main_okstate m s'
  (STEPS  : ConcreteProg.steps IMPL (m, ConcreteProg.get_fun_body IMPL 0 eq_refl tt) s'):
  ConcreteProg.okstate IMPL s'.
```
