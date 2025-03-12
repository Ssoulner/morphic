* What sort does Haskell use by default?
* Quite some reshaping had to be done to make 'tokens' work
* What to do with 'seq' in tokenPrimEx?
* In token, Parsec uses Integer instead of Int, becomes a problem for large numbers
* In token, we have to use Float instead of Double. Problem?
* In token (charLetter), what does 026 mean?
* In token, charNum needs to be implemented
* In token, charControl requires toEnum and fromEnum to be implemented
* In token, stringLetter uses 26b?