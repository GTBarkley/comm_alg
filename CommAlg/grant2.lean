import Mathlib.Order.KrullDimension
import Mathlib.Order.JordanHolder
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.Height
import Mathlib.RingTheory.Noetherian
import CommAlg.krull

variable {R : Type _} [CommRing R] [IsNoetherianRing R]

lemma height_le_of_gt_height_lt {n : ℕ∞} (q : PrimeSpectrum R)
  (h : ∀(p : PrimeSpectrum R), p < q → Ideal.height p ≤ n - 1) : Ideal.height q ≤ n := by
  sorry
   

theorem height_le_one_of_minimal_over_principle (p : PrimeSpectrum R) (x : R):
  p ∈ minimals (· < ·) {p | x ∈ p.asIdeal} → Ideal.height p ≤ 1 := by
  intro h
  -- apply height_le_of_gt_height_lt _ p
  -- intro q qlep
  -- by_contra hcontr
  -- push_neg at hcontr
  -- simp only [le_refl, tsub_eq_zero_of_le] at hcontr 
  
  sorry

#check (_ : Ideal R) ^ (_ : ℕ)
#synth Pow (Ideal R) (ℕ)

def symbolicIdeal (Q : Ideal R) [hin : Q.IsPrime] (I : Ideal R) : Ideal R where
  carrier := {r : R | ∃ s : R, s ∉ Q ∧ s * r ∈ I}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, mul_zero, Submodule.zero_mem, and_true]
    use 1
    rw [←Q.ne_top_iff_one]
    exact hin.ne_top
  add_mem' := by
    rintro a b ⟨sa, hsa1, hsa2⟩ ⟨sb, hsb1, hsb2⟩
    use sa * sb
    constructor
    . intro h
      cases hin.mem_or_mem h <;> contradiction
    ring_nf
    apply I.add_mem --<;> simp only [I.mul_mem_left, hsa2, hsb2]
    . rw [mul_comm sa, mul_assoc]
      exact I.mul_mem_left sb hsa2 
    . rw [mul_assoc]
      exact I.mul_mem_left sa hsb2
  smul_mem' := by
    intro c x
    dsimp
    rintro ⟨s, hs1, hs2⟩
    use s
    constructor; exact hs1
    rw [←mul_assoc, mul_comm s, mul_assoc]
    exact Ideal.mul_mem_left _ _ hs2

theorem Noetherian.height_zero_iff_symbolicPower_eq [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] :
  (∃ n : ℕ, symbolicIdeal P (P ^ n) = symbolicIdeal P (P ^ n.succ)) ↔ Ideal.height ⟨P, inferInstance⟩ = 0 := sorry

theorem WF_interval_le_prime [IsNoetherianRing R] (I : Ideal R) (P : Ideal R) [P.IsPrime] 
  (h : ∀ J ∈ (Set.Icc I P), J.IsPrime → J = P ):
  WellFounded ((· < ·) : (Set.Icc I P) → (Set.Icc I P) → Prop ) := sorry 

-- theorem smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson {I J : Ideal R} {N N' : Submodule R M}
--     (hN' : N'.FG) (hIJ : I ≤ jacobson J) (hNN : N ⊔ N' ≤ N ⊔ I • N') : N ⊔ I • N' = N ⊔ J • N' := sorry

lemma nakaka {N N' I P : Ideal R} [P.IsPrime] [IsNoetherianRing R]
  (hIP : I ≤ P) (hN : N ≤ P) (hNN : N ⊔ N' ≤ N ⊔ I • N') : N ⊔ I • N' = N := sorry 

lemma symbolicPower_one (Q : Ideal R) [Q.IsPrime] : symbolicIdeal Q (Q ^ 1) = Q := sorry
lemma symbolicPower_subset (Q : Ideal R) [Q.IsPrime] {n m : ℕ} (h : m ≤ n) : symbolicIdeal Q (Q ^ n) ≤ symbolicIdeal Q (Q ^ m) := sorry

protected lemma LocalRing.height_le_one_of_minimal_over_principle
  [LocalRing R] {x : R} 
  (h : (closedPoint R).asIdeal ∈ (Ideal.span {x}).minimalPrimes) :
  Ideal.height (closedPoint R) ≤ 1 := by
  -- by_contra hcont
  -- push_neg at hcont
  -- rw [Ideal.lt_height_iff'] at hcont
  -- rcases hcont with ⟨c, hc1, hc2, hc3⟩
  apply height_le_of_gt_height_lt
  intro Q hQ
  let I := Ideal.span {x}
  let P := (closedPoint R).asIdeal
  have artint : WellFounded ((· < ·) : (Set.Icc I P) → (Set.Icc I P) → Prop ) := by
    apply WF_interval_le_prime I P
    intro J hJ hJPr
    symm
    apply eq_of_mem_minimals h
    . exact ⟨hJPr, hJ.1⟩ 
    . exact hJ.2
  let fQ (n : ℕ) : Ideal R := symbolicIdeal Q.asIdeal (Q.asIdeal ^ n)
  have : ∃ n, I ⊔ fQ n = I ⊔ fQ (n.succ) := sorry
  simp only [le_refl, tsub_eq_zero_of_le, nonpos_iff_eq_zero]
  apply (Noetherian.height_zero_iff_symbolicPower_eq _).mp
  obtain ⟨n, hn⟩ := this
  use n
  have : fQ n.succ ⊔ I • fQ n = fQ n := sorry
  show fQ n = fQ n.succ
  rw [←this]
  apply nakaka (P := P)-- (N := symbolicIdeal Q.asIdeal (Q.asIdeal ^ n.succ)) (N' := symbolicIdeal Q.asIdeal (Q.asIdeal ^ n)) (I := I) (P := P)
  . exact h.1.2
  . calc
    _ ≤ fQ 1 := symbolicPower_subset Q.asIdeal (by show 1 ≤ n + 1; simp only [le_add_iff_nonneg_left, zero_le] : 1 ≤ n.succ)
    _ = Q.asIdeal := symbolicPower_one _
    _ ≤ P := le_of_lt hQ
  . suffices fQ n = fQ n.succ ⊔ I • fQ n by
      rw [←this, sup_eq_right.mpr]
      exact symbolicPower_subset Q.asIdeal (by show _ ≤ n + 1; simp : n ≤ n.succ)
    symm
    assumption