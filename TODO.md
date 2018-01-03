This development reflects authors' Coq learning experience and contain
lot of non-elegant and redundant code. Additionally, it includes some
workarounds for bugs and limitations for older Coq versions (starting
from 8.4).

It is overdue for serious refactoring and cleanup. Amongst other things:

* Review `_arg_proper` vs `_proper` instances
* In many cases `Equiv` instance is enough where `Setoid` is now required
* Some other cleanup opportunities are marked with "TODO" comments
* Proof-irrelevance assumption could be avoided
* Many usused definitions could be removed. (Hint: try `make print-unused`)


