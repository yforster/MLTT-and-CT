This is a roadmap for helping the [LogRel](https://github.com/CoqHott/logrel-mltt/) endeavor reach the state needed for the purpose of the formal study of CTTT.

1. take over the proof of the fundamental lemma of the logical relation (current state: stability by renaming done), for the current system (CCω), which itself decomposes in
    1. defining "validity", ie reducibility under any reducible substitution
    2. showing that this thing has all the properties corresponding to the (declarative) typing rules
    3. put all of 1.ii together to get the fundamental lemma
    4. prove the consequences currently conjectured in `LogRelConsequences.v`
3. extend the system with the empty type, unit, nat
4. extend the system with Σ (maybe using Abel's trick to factor the binder bureaucracy of Π and Σ via a boolean flag)

At this point, we should have reached a state in which we can fork the development, so as to add the constants needed for CTTT (quote). 
PMP suggests that we use integers as codes, and axiomatize their conversion to more convenient ones, so as to keep the formalization tractable (hopefully).

Once stated, it should be possible to work on 1.ii, 1.iii and 1.iv in parallel.
