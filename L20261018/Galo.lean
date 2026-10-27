import L20261018.A
/-!
# Carrier instances for the paper's coefficient object `μ_p`

`A.lean` already contains the paper's coefficient setup — `GaloBase.muP` (the trivial `ZMod p`-module
`μ_p` as a topological `G_F`-representation), the multiplication pairing `muPairing`, the classes
`V = H¹(G_F, μ_p)` and `H²`, the cup product `cup = muPairing.cup 1 1`, its skew-symmetry
`cup_skew`, and the instantiation `L20261018.galoBiKummer` of the abstract `BiKummerData` at the real
cup.

This file used to duplicate all of that. It now only adds what `A.lean` does not need but the
downstream files do: the **multiplicative instances on the carrier** `ZMod p`, which let the
coefficient identity `mul_assoc` be stated *at the carrier type* (`inferInstanceAs` unfolds the
definition of `muP`, which instance search will not do).
-/

set_option maxHeartbeats 1000000

open TauCeti

namespace GaloBase

variable (K : Type) [Field K] (p : ℕ) [Fact p.Prime]

instance : Semigroup (muP K p).V := inferInstanceAs (Semigroup (ZMod p))
instance : Monoid (muP K p).V := inferInstanceAs (Monoid (ZMod p))

end GaloBase
