/-
We don't want to reinvent the wheel, but finding
things in Mathlib can be pretty annoying. This is
a temporary file intended to be a dumping ground for
useful lemmas and definitions
-/
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.Artinian
import Mathlib.Order.Height

variable {R M : Type _} [CommRing R] [AddCommGroup M] [Module R M]

--ideals are defined
#check Ideal R

variable (I : Ideal R)

--as are prime and maximal (they are defined as typeclasses)
#check (I.IsPrime)
#check (I.IsMaximal)

--a module being Noetherian is also a class
#check IsNoetherian M
#check IsNoetherian I

--a ring is Noetherian if it is Noetherian as a module over itself
#check IsNoetherianRing R

--ditto for Artinian
#check IsArtinian M
#check IsArtinianRing R

--I can't find the theorem that an Artinian ring is noetherian. That could be a good
--thing to add at some point



--Here's the main defintion that will be helpful
#check Set.chainHeight