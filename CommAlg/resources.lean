/-
We don't want to reinvent the wheel, but finding
things in Mathlib can be pretty annoying. This is
a temporary file intended to be a dumping ground for
useful lemmas and definitions
-/
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.FiniteType
import Mathlib.Order.Height
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Algebra.Homology.ShortExact.Abelian

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

--this is the polynomial ring R[x]
#check Polynomial R
--this is the polynomial ring with variables indexed by ℕ
#check MvPolynomial ℕ R
--hopefully there's good communication between them


--There's a preliminary version of the going up theorem
#check Ideal.exists_ideal_over_prime_of_isIntegral

--Theorems relating primes of a ring to primes of its localization
#check PrimeSpectrum.localization_comap_injective
#check PrimeSpectrum.localization_comap_range
--Theorems relating primes of a ring to primes of a quotient
#check PrimeSpectrum.range_comap_of_surjective

--There's a lot of theorems about finite-type algebras
#check Algebra.FiniteType.polynomial
#check Algebra.FiniteType.mvPolynomial
#check Algebra.FiniteType.of_surjective

-- There is a notion of short exact sequences but the number of theorems are lacking
-- For example, I couldn't find anything saying that for a ses 0 -> A -> B -> C -> 0
-- of R-modules, A and C being FG implies that B is FG
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable {𝒜 : Type _} [Category 𝒜] [Abelian 𝒜]
variable {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C} {h : LeftSplit f g} {h' : RightSplit f g}

#check ShortExact
#check ShortExact f g
-- There are some notion of splitting as well
#check Splitting
#check LeftSplit
#check LeftSplit f g
-- And there is a theorem that left split implies splitting
#check LeftSplit.splitting
#check LeftSplit.splitting h
-- Similar things are there for RightSplit as well
#check RightSplit.splitting
#check RightSplit.splitting h'
-- There's also a theorem about ismorphisms between short exact sequences
#check isIso_of_shortExact_of_isIso_of_isIso
