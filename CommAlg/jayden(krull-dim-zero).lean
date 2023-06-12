import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Noetherian
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic

variable {R : Type _} [CommRing R]

-- Repeats the definition by Monalisa
noncomputable def length : krullDim (Submodule _ _)


-- The following is Stacks Lemma 10.60.5
lemma dim_zero_Noetherian_iff_Artinian (R : Type _) [CommRing R] : 
    IsNoetherianRing R ∧ krull_dim R = 0 ↔ IsArtinianRing R := by 
  sorry

#check IsNoetherianRing

-- The following is Stacks Lemma 10.53.6
lemma IsArtinian_iff_finite_length : IsArtinianRing R ↔ ∃ n : ℕ, length R R ≤ n := by sorry 






