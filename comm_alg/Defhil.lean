import Mathlib
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal




variable {R : Type _} (M A B C : Type _) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]


#check (A B : Submodule _ _) → (A ≤ B)

#check Preorder (Submodule _ _)

#check krullDim (Submodule _ _)

noncomputable def length := Set.chainHeight {M' : Submodule R M | M' < ⊤}

open LinearMap

#check length M



--lemma length_additive_shortexact {f : A ⟶ B} {g : B ⟶ C} (h : ShortExact f g) : length B = length A + length C := sorry

