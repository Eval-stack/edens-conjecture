# edens-conjecture

We resolve Eden's Conjecture

The Eden statements (all 4 variants) are formally refuted in Lean.

we're still working on kuznetsov-eden.


# Disclaimer for Eden's Conjecture

There are many competing definitions for the local Lyapunov dimension of a dynamical system, like for instance the Kuznetsov–Reitmann definition, the Kaplan–Yorke formula from upper singular-value exponents, and the Kaplan–Yorke formula from relative upper exponents. In the counterexample given, the different definitions agree. We verified this by checking convergence of every singular-value growth rate, which is a sufficient condition for these 3 definitions to agree. We do this in `EdensConjecture/DefinitionCheck.lean`. The actual Eden's Conjecture statements are found in `EdensConjecture/EStatements.lean`.

# Instructions

Install Lean 4.33.1, and from your directory run in powershell:

```powershell
lake build
```

The build completed successfully under Lean 4.33.1 in our session. There are no `admit`, `native_decide`, nor user-created axioms. There are instances of `sorry`, but they only come from Kuznetsov–Eden, which we're leaving unfinished indefinitely since we're busy with research (actual research under a mentor lmao).


# Credit

Evan Li, Lily Zhang.
Much of the counterexample construction was assisted by GPT-6 Astra. The authors independently searched the literature to verify the findings and discern the valid statements to use.