import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Order.Height
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Localization.AtPrime

/- This file contains the definitions of height of an ideal, and the krull
  dimension of a commutative ring.
  There are also sorried statements of many of the theorems that would be
  really nice to prove.
  I'm imagining for this file to ultimately contain basic API for height and
  krull dimension, and the theorems will probably end up other files,
  depending on how long the proofs are, and what extra API needs to be
  developed.
-/

variable {R : Type _} [CommRing R] (I : Ideal R)

namespace ideal

noncomputable def height : ℕ∞ := Set.chainHeight {J | J ≤ I ∧ J.IsPrime}

noncomputable def krull_dim (R : Type _) [CommRing R] := height (⊤ : Ideal R)

--some propositions that would be nice to be able to eventually

lemma dim_eq_zero_iff_field : krull_dim R = 0 ↔ IsField R := sorry

#check Ring.DimensionLEOne
lemma dim_le_one_iff : krull_dim R ≤ 1 ↔ Ring.DimensionLEOne R := sorry

lemma dim_le_one_of_pid [IsDomain R] [IsPrincipalIdealRing R] : krull_dim R ≤ 1 := sorry

lemma dim_le_dim_polynomial_add_one [Nontrivial R] :
  krull_dim R ≤ krull_dim (Polynomial R) + 1 := sorry

lemma dim_eq_dim_polynomial_add_one [Nontrivial R] [IsNoetherianRing R] :
  krull_dim R = krull_dim (Polynomial R) + 1 := sorry

lemma height_eq_dim_localization [Ideal.IsPrime I] :
  height I = krull_dim (Localization.AtPrime I) := sorry

lemma height_add_dim_quotient_le_dim : height I + krull_dim (R ⧸ I) ≤ krull_dim R := sorry