This is a roadmap for helping the logrel endeavor reach the state needed for the purpose of the formal study of CTTT.

1. take over the proof of stability by substitution of the logical relation (current state: stability by renaming done), for the current system (CCω)
2. extend the system with the empty type, unit, nat
3. extend the system with Σ (maybe using Abel's trick to factor the binder bureaucracy of Π and Σ via a boolean flag)

At this point, we should have reached a state in which we can fork the development, so as to add the constants needed for CTTT (quote). 
PMP suggests that we use integers as codes, and axiomatize their conversion to more convenient ones, so as to keep the formalization tractable (hopefully).

Now 1. decomposes into
1.1. defining "validity", ie reducibility under any reducible substitution
1.2. showing that this thing has all the properties corresponding to the (declarative) typing rules
1.3. put all of 1.2 together to get the fundamental lemma
1.4. prove the consequences currently conjectured in `LogRelConsequences.v`

Once stated, it should be possible to work on 1.2 and 1.3 in parallel.
