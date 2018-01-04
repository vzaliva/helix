This development reflects authors' Coq learning experience and contain
lot of non-elegant and redundant code. Additionally, it includes some
workarounds for bugs and limitations for older Coq versions (starting
from 8.4).

It is overdue for serious refactoring and cleanup. Amongst other things:

* Review `_arg_proper` vs `_proper` instances
* Some other cleanup opportunities are marked with "TODO" comments
* Proof-irrelevance assumption could be avoided
* Many usused definitions could be removed. (Hint: try `make print-unused`)
* `Vnth_proper` (to replace `Vnth_aux_arg_proper`)


