import CommAlg.krull
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.FiniteType
import Mathlib.Order.Height
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Ideal.MinimalPrime
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace Ideal

lemma polynomial_over_field_dim_one {K : Type} [Nontrivial K] [Field K] : krullDim (Polynomial K) = 1 := by
  -- unfold krullDim
  rw [le_antisymm_iff]
  constructor
  · 
    sorry
  · suffices : ∃I : PrimeSpectrum (Polynomial K), 1 ≤ (height I : WithBot ℕ∞)
    · obtain ⟨I, h⟩ := this
      have :  (height I : WithBot ℕ∞) ≤ ⨆ (I : PrimeSpectrum (Polynomial K)), ↑(height I) := by
        apply @le_iSup (WithBot ℕ∞) _ _ _ I
      exact le_trans h this
    have primeX : Prime Polynomial.X := @Polynomial.prime_X K _ _
    let X := @Polynomial.X K _
    have : IsPrime (span {X}) := by
      refine Iff.mpr (span_singleton_prime ?hp) primeX
      exact Polynomial.X_ne_zero
    let P := PrimeSpectrum.mk (span {X}) this
    unfold height
    use P
    have : ⊥ ∈ {J | J < P} := by
      simp only [Set.mem_setOf_eq]
      rw [bot_lt_iff_ne_bot]
      suffices : P.asIdeal ≠ ⊥
      · by_contra x
        rw [PrimeSpectrum.ext_iff] at x
        contradiction
      by_contra x
      simp only [span_singleton_eq_bot] at x
      have := @Polynomial.X_ne_zero K _ _
      contradiction
    have : {J | J < P}.Nonempty := Set.nonempty_of_mem this
    rwa [←Set.one_le_chainHeight_iff, ←WithBot.one_le_coe] at this
