Possible improvements
=========================================

### Underlying separation logic

Currently we use a toy program model and separation logic. But the interface,
tactics and functional representation are mostly independent of the underlying
separation logic. Hence one could try to parametrize the whole development by the
underlying separation logic.

One may need to introduce support for some notions of more advanced separation
logic in the functional translation. For instance, with a step-indexed
logic, one would probably want the latter modality to benefit from special
handling.

### Concurrency

Contrary to Steel, SLFun does not allow reasoning about concurrent programs.
As mentioned in the comparison with Steel, doing so would not only require a
change of the underlying separation logic but also additional verifications in
the interface (checking that invariants are not opened twice and only around
atomic instructions).
It could be interesting to try to support some kind of more general atomicity
(such as logical atomicity) rather than only a fixed notion of atomicity like
Steel does.
