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

lemma height_le_of_le {I J : PrimeSpectrum R} (I_le_J : I ≤ J) : height I ≤ height J := sorry -- Already done in main file

lemma dim_eq_dim_polynomial_add_one [Nontrivial R] [IsNoetherianRing R] :
  krullDim R + 1 = krullDim (Polynomial R) := by
  rw [le_antisymm_iff]
  constructor
  · exact dim_le_dim_polynomial_add_one
  · unfold krullDim
    have htPBdd : ∀ (P : PrimeSpectrum (Polynomial R)), (height P : WithBot ℕ∞) ≤ (⨆ (I : PrimeSpectrum R), ↑(height I + 1)) := by
      intro P
      have : ∃ (I : PrimeSpectrum R), (height P : WithBot ℕ∞) ≤ ↑(height I + 1) := by
        have : ∃ M, Ideal.IsMaximal M ∧ P.asIdeal ≤ M := by
          apply exists_le_maximal
          apply IsPrime.ne_top
          apply P.IsPrime
        obtain ⟨M, maxM, PleM⟩ := this
        let P' : PrimeSpectrum (Polynomial R) := PrimeSpectrum.mk M (IsMaximal.isPrime maxM)
        have PleP' : P ≤ P' := PleM
        have : height P ≤ height P' := height_le_of_le PleP'
        simp only [WithBot.coe_le_coe]
        have : ∃ (I : PrimeSpectrum R), height P' ≤ height I + 1 := by

          sorry
        obtain ⟨I, h⟩ := this
        use I
        exact ge_trans h this
      obtain ⟨I, IP⟩ := this
      have : (↑(height I + 1) : WithBot ℕ∞) ≤ ⨆ (I : PrimeSpectrum R), ↑(height I + 1) := by
        apply @le_iSup (WithBot ℕ∞) _ _ _ I
      exact ge_trans this IP
    have oneOut : (⨆ (I : PrimeSpectrum R), (height I : WithBot ℕ∞) + 1) ≤ (⨆ (I : PrimeSpectrum R), ↑(height I)) + 1 := by
      have : ∀ P : PrimeSpectrum R, (height P : WithBot ℕ∞) + 1 ≤ (⨆ (I : PrimeSpectrum R), ↑(height I)) + 1 :=
        fun P ↦ (by apply add_le_add_right (@le_iSup (WithBot ℕ∞) _ _ _ P) 1)
      apply iSup_le
      apply this
    simp only [iSup_le_iff]
    intro P
    exact ge_trans oneOut (htPBdd P)
