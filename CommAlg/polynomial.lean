import CommAlg.krull

section ChainLemma
variable {α β : Type _}
variable [LT α] [LT β] (s t : Set α)

namespace Set
open List

/-
Sorry for using aesop, but it doesn't take that long
-/
theorem append_mem_subchain_iff :
l ++ l' ∈ s.subchain ↔ l ∈ s.subchain ∧ l' ∈ s.subchain ∧ ∀ a ∈ l.getLast?, ∀ b ∈ l'.head?, a < b := by
  simp [subchain, chain'_append]
  aesop

end Set
end ChainLemma

variable {R : Type _} [CommRing R]
open Ideal Polynomial

namespace Polynomial
/-
The composition R → R[X] → R is the identity
-/
theorem coeff_C_eq : RingHom.comp constantCoeff C = RingHom.id R := by ext; simp

end Polynomial

/-
Given an ideal I in R, we define the ideal adjoin_x' I to be the kernel
of R[X] → R → R/I
-/
def adj_x_map (I : Ideal R) : R[X] →+* R ⧸ I := (Ideal.Quotient.mk I).comp constantCoeff
def adjoin_x' (I : Ideal R) : Ideal (Polynomial R) := RingHom.ker (adj_x_map I)
def adjoin_x (I : PrimeSpectrum R) : PrimeSpectrum (Polynomial R) where
  asIdeal := adjoin_x' I.asIdeal
  IsPrime := RingHom.ker_isPrime _

@[simp]
lemma adj_x_comp_C (I : Ideal R) : RingHom.comp (adj_x_map I) C = Ideal.Quotient.mk I := by
  ext x; simp [adj_x_map]

lemma adjoin_x_eq (I : Ideal R) : adjoin_x' I = I.map C ⊔ Ideal.span {X} := by
  apply le_antisymm
  . rintro p hp
    have h : ∃ q r, p = C r + X * q := ⟨p.divX, p.coeff 0, p.divX_mul_X_add.symm.trans $ by ring⟩
    obtain ⟨q, r, rfl⟩ := h
    suffices : r ∈ I
    . simp only [Submodule.mem_sup, Ideal.mem_span_singleton]
      refine' ⟨C r, Ideal.mem_map_of_mem C this, X * q, ⟨q, rfl⟩, rfl⟩
    rw [adjoin_x', adj_x_map, RingHom.mem_ker, RingHom.comp_apply] at hp
    rw [constantCoeff_apply, coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero] at hp
    rwa  [←RingHom.mem_ker, Ideal.mk_ker] at hp
  . rw [sup_le_iff]
    constructor
    . simp [adjoin_x', RingHom.ker, ←map_le_iff_le_comap, Ideal.map_map]
    . simp [span_le, adjoin_x', RingHom.mem_ker, adj_x_map]

/-
If I is prime in R, the pushforward I*R[X] is prime in R[X]
-/
def map_prime (I : PrimeSpectrum R) : PrimeSpectrum R[X] :=
  ⟨I.asIdeal.map C, isPrime_map_C_of_isPrime I.IsPrime⟩

/-
The pushforward map (Ideal R) → (Ideal R[X]) is injective
-/
lemma map_inj {I J : Ideal R} (h : I.map C = J.map C) : I = J := by
  have H : map constantCoeff (I.map C) = map constantCoeff (J.map C) := by rw [h]
  simp [Ideal.map_map, coeff_C_eq] at H
  exact H

/-
The pushforward map (Ideal R) → (Ideal R[X]) is strictly monotone
-/
lemma map_strictmono {I J : Ideal R} (h : I < J) : I.map C < J.map C := by
  rw [lt_iff_le_and_ne] at h ⊢
  exact ⟨map_mono h.1, fun H => h.2 (map_inj H)⟩

lemma map_lt_adjoin_x (I : PrimeSpectrum R) : map_prime I < adjoin_x I := by
  simp [adjoin_x, adjoin_x_eq]
  show I.asIdeal.map C  < I.asIdeal.map C ⊔ span {X}
  simp [Ideal.span_le, mem_map_C_iff]
  use 1
  simp
  rw [←Ideal.eq_top_iff_one]
  exact I.IsPrime.ne_top'

lemma ht_adjoin_x_eq_ht_add_one [Nontrivial R] (I : PrimeSpectrum R) : height I + 1 ≤ height (adjoin_x I) := by
  suffices H : height I + (1 : ℕ) ≤ height (adjoin_x I) + (0 : ℕ)
  . norm_cast at H; rw [add_zero] at H; exact H
  rw [height, height, Set.chainHeight_add_le_chainHeight_add {J | J < I} _ 1 0]
  intro l hl
  use ((l.map map_prime) ++ [map_prime I])
  refine' ⟨_, by simp⟩
  . simp [Set.append_mem_subchain_iff]
    refine' ⟨_, map_lt_adjoin_x I, fun a ha => _⟩
    . refine' ⟨_, fun i hi => _⟩
      . apply List.chain'_map_of_chain' map_prime (fun a b hab => map_strictmono hab) hl.1
      . rw [List.mem_map] at hi
        obtain ⟨a, ha, rfl⟩ := hi
        calc map_prime a < map_prime I := by apply map_strictmono; apply hl.2; apply ha
          _ < adjoin_x I := by apply map_lt_adjoin_x
    . have H : ∃ b : PrimeSpectrum R, b ∈ l ∧ map_prime b = a
      . have H2 : l ≠ []
        . intro h
          rw [h] at ha
          tauto
        use l.getLast H2
        refine' ⟨List.getLast_mem H2, _⟩
        have H3 : l.map map_prime ≠ []
        . intro hl
          apply H2
          apply List.eq_nil_of_map_eq_nil hl
        rw [List.getLast?_eq_getLast _ H3, Option.some_inj] at ha
        simp [←ha, List.getLast_map _ H2]
      obtain ⟨b, hb, rfl⟩ := H
      apply map_strictmono
      apply hl.2
      exact hb

/-
dim R + 1 ≤ dim R[X]
-/
lemma dim_le_dim_polynomial_add_one [Nontrivial R] :
  krullDim R + (1 : ℕ∞) ≤ krullDim R[X] := by
  obtain ⟨n, hn⟩ := krullDim_nonneg_of_nontrivial R
  rw [hn]
  change ↑(n + 1) ≤ krullDim R[X]
  have := le_of_eq hn.symm
  induction' n using ENat.recTopCoe with n
  . change krullDim R = ⊤ at hn
    change ⊤ ≤ krullDim R[X] 
    rw [krullDim_eq_top_iff] at hn
    rw [top_le_iff, krullDim_eq_top_iff]
    intro n
    obtain ⟨I, hI⟩ := hn n
    use adjoin_x I
    calc n ≤ height I := hI
      _ ≤ height I + 1 := le_self_add
      _ ≤ height (adjoin_x I) := ht_adjoin_x_eq_ht_add_one I
  change n ≤ krullDim R at this
  change (n + 1 : ℕ) ≤ krullDim R[X]
  rw [le_krullDim_iff] at this ⊢
  obtain ⟨I, hI⟩ := this
  use adjoin_x I
  apply WithBot.coe_mono
  calc n + 1 ≤ height I + 1 := by
        apply add_le_add_right
        change ((n : ℕ∞) : WithBot ℕ∞) ≤ (height I) at hI
        rw [WithBot.coe_le_coe] at hI
        exact hI
    _ ≤ height (adjoin_x I) := ht_adjoin_x_eq_ht_add_one I