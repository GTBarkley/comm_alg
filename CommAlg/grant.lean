import Mathlib.Order.KrullDimension
import Mathlib.Order.JordanHolder
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.Height
import CommAlg.krull


#check (p q : PrimeSpectrum _) → (p ≤ q)
#check Preorder (PrimeSpectrum _)

-- Dimension of a ring
#check krullDim (PrimeSpectrum _)

-- Length of a module
#check krullDim (Submodule _ _)

#check JordanHolderLattice


section Chains

variable {α : Type _} [Preorder α] (s : Set α)

def finFun_to_list {n : ℕ} : (Fin n → α) → List α := by sorry

def series_to_chain : StrictSeries s → s.subchain
| ⟨length, toFun, strictMono⟩ => 
    ⟨ finFun_to_list (fun x => toFun x),
      sorry⟩

-- there should be a coercion from WithTop ℕ to WithBot (WithTop ℕ) but it doesn't seem to work
-- it looks like this might be because someone changed the instance from CoeCT to Coe during the port
-- actually it looks like we can coerce to WithBot (ℕ∞) fine
lemma twoHeights : s ≠ ∅ → (some (Set.chainHeight s) : WithBot (WithTop ℕ)) = krullDim s := by
  intro hs
  unfold Set.chainHeight
  unfold krullDim
  have hKrullSome : ∃n, krullDim s = some n := by
    
    sorry
  -- norm_cast
  sorry

end Chains

section Krull

variable (R : Type _) [CommRing R] (M : Type _) [AddCommGroup M] [Module R M]

open Ideal

-- chain of primes 
#check height 

lemma lt_height_iff {𝔭 : PrimeSpectrum R} {n : ℕ∞} :
  height 𝔭 > n ↔ ∃ c : List (PrimeSpectrum R), c ∈ {I : PrimeSpectrum R | I < 𝔭}.subchain ∧ c.length = n + 1 := sorry

lemma lt_height_iff' {𝔭 : PrimeSpectrum R} {n : ℕ∞} : 
height 𝔭 > n ↔ ∃ c : List (PrimeSpectrum R), c.Chain' (· < ·) ∧ (∀ 𝔮 ∈ c, 𝔮 < 𝔭) ∧ c.length = n + 1 := by
  rcases n with _ | n
  . constructor <;> intro h <;> exfalso
    . exact (not_le.mpr h) le_top
    . -- change ∃c, _ ∧ _ ∧ ((List.length c : ℕ∞) = ⊤ + 1) at h
      -- rw [WithTop.top_add] at h
      tauto
  have (m : ℕ∞) : m > some n ↔ m ≥ some (n + 1) := by
    symm
    show (n + 1 ≤ m ↔ _ )
    apply ENat.add_one_le_iff
    exact ENat.coe_ne_top _
  rw [this]
  unfold Ideal.height
  show ((↑(n + 1):ℕ∞) ≤ _) ↔ ∃c, _ ∧ _ ∧ ((_ : WithTop ℕ) = (_:ℕ∞))
  rw [{J | J < 𝔭}.le_chainHeight_iff]
  show (∃ c, (List.Chain' _ c ∧ ∀𝔮, 𝔮 ∈ c → 𝔮 < 𝔭) ∧ _) ↔ _
  -- have h := fun (c : List (PrimeSpectrum R)) => (@WithTop.coe_eq_coe _ (List.length c) n) 
  constructor <;> rintro ⟨c, hc⟩ <;> use c --<;> tauto--<;> exact ⟨hc.1, by tauto⟩
  . --rw [and_assoc]
    -- show _ ∧ _ ∧ _
    --exact ⟨hc.1, _⟩
    tauto
  . change _ ∧ _ ∧ (List.length c : ℕ∞) = n + 1 at hc
    norm_cast at hc
    tauto

lemma krullDim_nonneg_of_nontrivial [Nontrivial R] : ∃ n : ℕ∞, Ideal.krullDim R = n := by
  have h := dim_eq_bot_iff.not.mpr (not_subsingleton R)
  lift (Ideal.krullDim R) to ℕ∞ using h with k
  use k

-- lemma krullDim_le_iff' (R : Type _) [CommRing R] {n : WithBot ℕ∞} : 
--   Ideal.krullDim R ≤ n ↔ (∀ c : List (PrimeSpectrum R), c.Chain' (· < ·) → c.length ≤ n + 1) := by
--     sorry

-- lemma krullDim_ge_iff' (R : Type _) [CommRing R] {n : WithBot ℕ∞} : 
--   Ideal.krullDim R ≥ n ↔ ∃ c : List (PrimeSpectrum R), c.Chain' (· < ·) ∧ c.length = n + 1 := sorry

lemma prime_elim_of_subsingleton (x : PrimeSpectrum R) [Subsingleton R] : False :=
  x.1.ne_top_iff_one.1 x.2.1 <| Eq.substr (Subsingleton.elim 1 (0 : R)) x.1.zero_mem

lemma primeSpectrum_empty_iff : IsEmpty (PrimeSpectrum R) ↔ Subsingleton R := by
  constructor
  . contrapose
    rw [not_isEmpty_iff, ←not_nontrivial_iff_subsingleton, not_not]
    apply PrimeSpectrum.instNonemptyPrimeSpectrum
  . intro h
    by_contra hneg
    rw [not_isEmpty_iff] at hneg
    rcases hneg with ⟨a, ha⟩
    exact prime_elim_of_subsingleton R ⟨a, ha⟩

lemma dim_eq_bot_iff : krullDim R = ⊥ ↔ Subsingleton R := by
  unfold Ideal.krullDim
  rw [←primeSpectrum_empty_iff, iSup_eq_bot]
  constructor <;> intro h
  . rw [←not_nonempty_iff]
    rintro ⟨a, ha⟩
    specialize h ⟨a, ha⟩
    tauto
  . rw [h.forall_iff]
    trivial


#check (sorry : False)
#check (sorryAx)
#check (4 : WithBot ℕ∞)
#check List.sum
-- #check ((4 : ℕ∞) : WithBot (WithTop ℕ))
-- #check ( (Set.chainHeight s) : WithBot (ℕ∞))

variable (P : PrimeSpectrum R)

#check {J | J < P}.le_chainHeight_iff (n := 4)
