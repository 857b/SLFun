From SLFun.VProg Require Export Vprop Core Ghost Instructions.

Module Tactics.
  Export ConcreteProg.Tactics.
  Export VProg.Core.Tactics VProg.Ghost.Tactics VProg.Instructions.Tactics.
End Tactics.

Module Notations.
  Export Tactics.
  Export VProg.Core.Notations.
End Notations.
