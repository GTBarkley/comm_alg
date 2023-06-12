import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic

lemma quotientRing_is_Artinian (R : Type _) [CommRing R] (I : Ideal R) (IsArt : IsArtinianRing R): 
IsArtinianRing (R⧸I) := by sorry

#check Ideal.IsPrime

lemma IsPrimeMaximal (R : Type _) [CommRing R] (I : Ideal R) (IsArt : IsArtinianRing R) (isPrime : Ideal.IsPrime I) : Ideal.IsMaximal I := by sorry


-- Use Stacks project proof since it's broken into lemmas
