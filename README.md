## Proof Checker
This proof checker takes intuitionnist logic human-written proof trees, and check its correction

# How To Use
There are OCaml functions, usable thanks to utop

The three main functions are :
    - the lexer, which tokenizes the written proof
    - the parser "parse", which parses the token list (given by the lexer) into a proof tree
    - the checker, which checks the correction of a proof tree

Most of the time, these three functions are to be used consecutively, thanks to "check_string"

# Miscellaneous

Some examples of the syntax of the written proofs are in "test.txt"

This project is fully free for use and modification 

As I am French, a part of the code is written in French

# Future upgrades
- Add the classical logic (proof by contradiction, double negation elimination, excluded middle)
- Implement forst-order logic
- Code a partially correct brute-force alogorithm to automatically prove correct formulae (incorrect ones would cause the machine to loop)

