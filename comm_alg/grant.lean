import Mathlib.Order.KrullDimension
import Mathlib.Order.JordanHolder
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.Height


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
lemma twoHeights : s ≠ ∅ → (some (Set.chainHeight s) : WithBot (WithTop ℕ)) = krullDim s := by
  intro hs
  unfold Set.chainHeight
  unfold krullDim
  have hKrullSome : ∃n, krullDim s = some n := by
    
    sorry
  -- norm_cast
  sorry

def krullDimGE (R : Type _) [CommRing R] (n : ℕ) :=
  ∃ c : List (PrimeSpectrum R), c.Chain' (· < ·) ∧ c.length = n + 1