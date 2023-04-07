Ltac symmetric_iff :=
  let H  := fresh "H"  in
  eassert _ as H; [|
    let Hs := fresh "Hs" in
    pose proof (Hs := H);
    repeat (let x := fresh "x" in intro x;
            refine (_ (Hs x)); clear Hs; intro Hs);
    split; [ exact Hs
           | eapply H; try solve [try symmetry; eassumption] ];
    clear H Hs
  ].

