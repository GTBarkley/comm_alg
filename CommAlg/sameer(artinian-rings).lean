import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Noetherian
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.DedekindDomain.DVR


lemma FieldisArtinian (R : Type _) [CommRing R] (h : IsField R) : 
    IsArtinianRing R := by
  let inst := h.toField
  rw [isArtinianRing_iff, isArtinian_iff_wellFounded]
  apply WellFounded.intro
  intro I
  constructor
  intro J hJI
  constructor
  intro K hKJ
  exfalso
  rcases Ideal.eq_bot_or_top J with rfl | rfl
  . exact not_lt_bot hKJ
  . exact not_top_lt hJI

lemma ArtinianDomainIsField (R : Type _) [CommRing R] [IsDomain R]
(IsArt : IsArtinianRing R) : IsField (R) := by 
-- Assume P is nonzero and R is Artinian
-- Localize at P; Then R_P is Artinian; 
-- Assume R_P is not a field 
-- Then Jacobson Radical of R_P is nilpotent so it's maximal ideal is nilpotent
-- Maximal ideal is zero since local ring is a domain
-- a contradiction since P is nonzero
-- Therefore, R is a field
have maxIdeal := Ideal.exists_maximal R
obtain ⟨m,hm⟩ := maxIdeal
have h:= Ideal.primeCompl_le_nonZeroDivisors m 
have artRP : IsDomain _ := IsLocalization.isDomain_localization h
have h' : IsArtinianRing (Localization (Ideal.primeCompl m)) := inferInstance
have h' : IsNilpotent (Ideal.jacobson (⊥ : Ideal (Localization 
  (Ideal.primeCompl m)))):= IsArtinianRing.isNilpotent_jacobson_bot
have := LocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal (Localization 
  (Ideal.primeCompl m))) bot_ne_top
rw [this] at h'
have := IsNilpotent.eq_zero h'
rw [Ideal.zero_eq_bot, ← LocalRing.isField_iff_maximalIdeal_eq] at this
by_contra h''
--by_cases h'' : m = ⊥
have := Ring.ne_bot_of_isMaximal_of_not_isField hm h'' 
have := IsLocalization.AtPrime.not_isField R this (Localization (Ideal.primeCompl m))
contradiction


#check Ideal.IsPrime
#check IsDomain

lemma isArtinianRing_of_quotient_of_artinian (R : Type _) [CommRing R]
    (I : Ideal R) (IsArt : IsArtinianRing R) : IsArtinianRing (R ⧸ I) :=
  isArtinian_of_tower R (isArtinian_of_quotient_of_artinian R R I IsArt)

lemma IsPrimeMaximal (R : Type _) [CommRing R] (P : Ideal R) 
(IsArt : IsArtinianRing R) (isPrime : Ideal.IsPrime P) : Ideal.IsMaximal P := 
by 
-- if R is Artinian and P is prime then R/P is Artinian Domain 
-- R⧸P is a field by the above lemma
-- P is maximal

  have : IsDomain (R⧸P) := Ideal.Quotient.isDomain P
  have artRP : IsArtinianRing (R⧸P) := by
    exact isArtinianRing_of_quotient_of_artinian R P IsArt
  
  have artRPField : IsField (R⧸P) := by
    exact ArtinianDomainIsField (R⧸P) artRP
  
  have h := Ideal.Quotient.maximal_of_isField P artRPField
  exact h
  
-- Then R/I is Artinian 
 --  have' : IsArtinianRing R ∧ Ideal.IsPrime I → IsDomain (R⧸I) := by

-- R⧸I.IsArtinian → monotone_stabilizes_iff_artinian.R⧸I
