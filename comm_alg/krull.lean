import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Order.Height
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic

/- This file contains the definitions of height of an ideal, and the krull
  dimension of a commutative ring.
  There are also sorried statements of many of the theorems that would be
  really nice to prove.
  I'm imagining for this file to ultimately contain basic API for height and
  krull dimension, and the theorems will probably end up other files,
  depending on how long the proofs are, and what extra API needs to be
  developed.
-/

namespace Ideal

variable {R : Type _} [CommRing R] (I : PrimeSpectrum R)

noncomputable def height : ℕ∞ := Set.chainHeight {J : PrimeSpectrum R | J ≤ I} - 1

noncomputable def krull_dim (R : Type) [CommRing R]: WithBot ℕ∞ := ⨆ (I : PrimeSpectrum R), height I

--some propositions that would be nice to be able to eventually

lemma dim_eq_zero_iff_field : krull_dim R = 0 ↔ IsField R := by sorry

#check Ring.DimensionLEOne
lemma dim_le_one_iff : krull_dim R ≤ 1 ↔ Ring.DimensionLEOne R := sorry

lemma dim_le_one_of_pid [IsDomain R] [IsPrincipalIdealRing R] : krull_dim R ≤ 1 := by
  rw [dim_le_one_iff]
  exact Ring.DimensionLEOne.principal_ideal_ring R

lemma dim_le_dim_polynomial_add_one [Nontrivial R] :
  krull_dim R ≤ krull_dim (Polynomial R) + 1 := sorry

lemma dim_eq_dim_polynomial_add_one [Nontrivial R] [IsNoetherianRing R] :
  krull_dim R = krull_dim (Polynomial R) + 1 := sorry

lemma height_eq_dim_localization :
  height I = krull_dim (Localization.AtPrime I.asIdeal) := sorry

lemma height_add_dim_quotient_le_dim : height I + krull_dim (R ⧸ I.asIdeal) ≤ krull_dim R := sorry