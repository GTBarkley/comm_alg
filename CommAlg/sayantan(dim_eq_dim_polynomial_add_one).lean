import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Order.Height
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace Ideal

variable {R : Type _} [CommRing R] (I : PrimeSpectrum R)
noncomputable def height : ℕ∞ := Set.chainHeight {J : PrimeSpectrum R | J < I}
noncomputable def krullDim (R : Type) [CommRing R] : WithBot ℕ∞ := ⨆ (I : PrimeSpectrum R), height I

lemma height_def : height I = Set.chainHeight {J : PrimeSpectrum R | J < I} := rfl
lemma krullDim_def (R : Type) [CommRing R] : krullDim R = (⨆ (I : PrimeSpectrum R), height I : WithBot ℕ∞) := rfl
lemma krullDim_def' (R : Type) [CommRing R] : krullDim R = iSup (λ I : PrimeSpectrum R => (height I : WithBot ℕ∞)) := rfl

noncomputable instance : CompleteLattice (WithBot (ℕ∞)) := WithBot.WithTop.completeLattice

lemma dim_le_dim_polynomial_add_one [Nontrivial R] :
  krullDim R + 1 ≤ krullDim (Polynomial R) := sorry -- Others are working on it

-- private lemma sum_succ_of_succ_sum {ι : Type} (a : ℕ∞) [inst : Nonempty ι] :
--       (⨆ (x : ι), a + 1) = (⨆ (x : ι), a) + 1 := by
--   have : a + 1 = (⨆ (x : ι), a) + 1 := by rw [ciSup_const]
--   have : a + 1 = (⨆ (x : ι), a + 1) := Eq.symm ciSup_const
--   simp

lemma dim_eq_dim_polynomial_add_one [Nontrivial R] [IsNoetherianRing R] :
  krullDim R + 1 = krullDim (Polynomial R) := by
  rw [le_antisymm_iff]
  constructor
  · exact dim_le_dim_polynomial_add_one
  · unfold krullDim
    have htPBdd : ∀ (P : PrimeSpectrum (Polynomial R)), (height P : WithBot ℕ∞) ≤ (⨆ (I : PrimeSpectrum R), ↑(height I + 1)) := by
      intro P
      have : ∃ (I : PrimeSpectrum R), (height P : WithBot ℕ∞) ≤ ↑(height I + 1) := by
        sorry
      obtain ⟨I, IP⟩ := this
      have : (↑(height I + 1) : WithBot ℕ∞) ≤ ⨆ (I : PrimeSpectrum R), ↑(height I + 1) := by
        apply @le_iSup (WithBot ℕ∞) _ _ _ I
      apply ge_trans this IP
    have oneOut : (⨆ (I : PrimeSpectrum R), (height I : WithBot ℕ∞) + 1) ≤ (⨆ (I : PrimeSpectrum R), ↑(height I)) + 1 := by
      have : ∀ P : PrimeSpectrum R, (height P : WithBot ℕ∞) + 1 ≤ (⨆ (I : PrimeSpectrum R), ↑(height I)) + 1 :=
        fun P ↦ (by apply add_le_add_right (@le_iSup (WithBot ℕ∞) _ _ _ P) 1)
      apply iSup_le
      apply this
    simp
    intro P
    exact ge_trans oneOut (htPBdd P)
