import CommAlg.krull
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Order.Height
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic

namespace Ideal

private lemma singleton_chainHeight_one {α : Type} [Preorder α] [Bot α] : Set.chainHeight {(⊥ : α)} ≤ 1 := by
  unfold Set.chainHeight
  simp only [iSup_le_iff, Nat.cast_le_one]
  intro L h
  unfold Set.subchain at h
  simp only [Set.mem_singleton_iff, Set.mem_setOf_eq] at h
  rcases L with (_ | ⟨a,L⟩)
  . simp only [List.length_nil, zero_le]
  rcases L with (_ | ⟨b,L⟩)
  . simp only [List.length_singleton, le_refl]
  simp only [List.chain'_cons, List.find?, List.mem_cons, forall_eq_or_imp] at h
  rcases h with ⟨⟨h1, _⟩,  ⟨rfl, rfl, _⟩⟩
  exact absurd h1 (lt_irrefl _)

/-- The ring of polynomials over a field has dimension one. -/
lemma polynomial_over_field_dim_one {K : Type} [Nontrivial K] [Field K] : krullDim (Polynomial K) = 1 := by
  rw [le_antisymm_iff]
  let X := @Polynomial.X K _
  constructor
  · unfold krullDim
    apply @iSup_le (WithBot ℕ∞) _ _ _ _
    intro I
    have PIR : IsPrincipalIdealRing (Polynomial K) := by infer_instance
    by_cases I = ⊥
    · rw [← height_bot_iff_bot] at h
      simp only [WithBot.coe_le_one, ge_iff_le]
      rw [h]
      exact bot_le
    · push_neg at h
      have : I.asIdeal ≠ ⊥ := by
        by_contra a
        have : I = ⊥ := PrimeSpectrum.ext I ⊥ a
        contradiction
      have maxI := IsPrime.to_maximal_ideal this
      have sngletn : ∀P, P ∈ {J | J < I} ↔ P = ⊥ := by
          intro P
          constructor
          · intro H
            simp only [Set.mem_setOf_eq] at H
            by_contra x
            push_neg at x
            have : P.asIdeal ≠ ⊥ := by
              by_contra a
              have : P = ⊥ := PrimeSpectrum.ext P ⊥ a
              contradiction 
            have maxP := IsPrime.to_maximal_ideal this
            have IneTop := IsMaximal.ne_top maxI
            have : P ≤ I := le_of_lt H
            rw [←PrimeSpectrum.asIdeal_le_asIdeal] at this
            have : P.asIdeal = I.asIdeal := Ideal.IsMaximal.eq_of_le maxP IneTop this
            have : P = I := PrimeSpectrum.ext P I this
            replace H : P ≠ I := ne_of_lt H
            contradiction
          · intro pBot
            simp only [Set.mem_setOf_eq, pBot]
            exact lt_of_le_of_ne bot_le h.symm
      replace sngletn : {J | J < I} = {⊥} := Set.ext sngletn
      unfold height
      rw [sngletn]
      simp only [WithBot.coe_le_one, ge_iff_le]
      exact singleton_chainHeight_one
  · suffices : ∃I : PrimeSpectrum (Polynomial K), 1 ≤ (height I : WithBot ℕ∞)
    · obtain ⟨I, h⟩ := this
      have :  (height I : WithBot ℕ∞) ≤ ⨆ (I : PrimeSpectrum (Polynomial K)), ↑(height I) := by
        apply @le_iSup (WithBot ℕ∞) _ _ _ I
      exact le_trans h this
    have primeX : Prime Polynomial.X := @Polynomial.prime_X K _ _
    have : IsPrime (span {X}) := by
      refine (span_singleton_prime ?hp).mpr primeX
      exact Polynomial.X_ne_zero
    let P := PrimeSpectrum.mk (span {X}) this
    unfold height
    use P
    have : ⊥ ∈ {J | J < P} := by
      simp only [Set.mem_setOf_eq, bot_lt_iff_ne_bot]
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
