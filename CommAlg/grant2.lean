import Mathlib.Order.KrullDimension
import Mathlib.Order.JordanHolder
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.Height
import Mathlib.RingTheory.Noetherian
import CommAlg.krull

variable (R : Type _) [CommRing R] [IsNoetherianRing R]

lemma height_le_of_gt_height_lt {n : ℕ∞} (q : PrimeSpectrum R)
  (h : ∀(p : PrimeSpectrum R), p < q → Ideal.height p ≤ n - 1) : Ideal.height q ≤ n := by
  sorry
   

theorem height_le_one_of_minimal_over_principle (p : PrimeSpectrum R) (x : R):
  p ∈ minimals (· < ·) {p | x ∈ p.asIdeal} → Ideal.height p ≤ 1 := by
  intro h
  apply height_le_of_gt_height_lt _ p
  intro q qlep
  by_contra hcontr
  push_neg at hcontr
  simp only [le_refl, tsub_eq_zero_of_le] at hcontr 
  
  sorry

#check (_ : Ideal R) ^ (_ : ℕ)
#synth Pow (Ideal R) (ℕ)

def symbolicIdeal(Q : Ideal R) {hin : Q.IsPrime} (I : Ideal R) : Ideal R where
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

protected lemma LocalRing.height_le_one_of_minimal_over_principle
  [LocalRing R] (q : PrimeSpectrum R) {x : R} 
  (h : (closedPoint R).asIdeal ∈ (Ideal.span {x}).minimalPrimes) :
  q = closedPoint R ∨ Ideal.height q = 0 := by
  
  sorry