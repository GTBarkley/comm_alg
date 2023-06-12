import Mathlib

variable {R : Type _} (M A B C : Type _) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
variable (A' B' C' : ModuleCat R)
#check ModuleCat.of R A

example : Module R A' := inferInstance

#check ModuleCat.of R B

example : Module R B' := inferInstance

#check ModuleCat.of R C

example : Module R C' := inferInstance

namespace CategoryTheory

noncomputable instance abelian : Abelian (ModuleCat.{v} R) := inferInstance
noncomputable instance haszero : Limits.HasZeroMorphisms (ModuleCat.{v} R) := inferInstance

#check (A B : Submodule _ _) → (A ≤ B)

#check Preorder (Submodule _ _)

#check krullDim (Submodule _ _)

noncomputable def length := krullDim (Submodule R M) 
 
open ZeroObject

namespace HasZeroMorphisms

open LinearMap

#check length M

#check ModuleCat.of R

lemma length_additive_shortexact {f : A ⟶ B} {g : B ⟶ C} (h : ShortExact f g) : length B = length A + length C := sorry

