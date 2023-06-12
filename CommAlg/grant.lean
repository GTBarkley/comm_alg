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

open Ideal

lemma krullDim_le_iff' (R : Type _) [CommRing R] : 
  Ideal.krullDim R ≤ n ↔ (∀ c : List (PrimeSpectrum R), c.Chain' (· < ·) → c.length ≤ n + 1) := by
    sorry

lemma krullDim_ge_iff' (R : Type _) [CommRing R] : 
  Ideal.krullDim R ≥ n ↔ ∃ c : List (PrimeSpectrum R), c.Chain' (· < ·) ∧ c.length = n + 1 := sorry


-- #check ((4 : ℕ∞) : WithBot (WithTop ℕ))
#check ( (Set.chainHeight s) : WithBot (ℕ∞))