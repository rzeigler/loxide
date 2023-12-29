# loxide

[Crafting Interpreters](http://craftinginterpreters.com/) implemented in Rust

## Things I should solve at some point.

The scanner is super awkwardly implemented as an iterator.
This is awkward because the scanner wraps around a peekable char iterator but is also used as a peekable.
Additionally, having an explicit EOF is nice, but is duplicative with None from the iterator protocol.
There's also lots of weird complications from checking the next token, etc.
