import Mathlib.Order.Height
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic

-- Setting for "library_search"
set_option maxHeartbeats 0
macro "ls" : tactic => `(tactic|library_search)

-- New tactic "obviously"
macro "obviously" : tactic =>
  `(tactic| (
      first
        | dsimp; simp; done; dbg_trace "it was dsimp simp"
        | simp; done; dbg_trace "it was simp"
        | tauto; done; dbg_trace "it was tauto"
        | simp; tauto; done; dbg_trace "it was simp tauto"
        | rfl; done; dbg_trace "it was rfl"
        | norm_num; done; dbg_trace "it was norm_num"
        | /-change (@Eq ℝ _ _);-/ linarith; done; dbg_trace "it was linarith"
        -- | gcongr; done
        | ring; done; dbg_trace "it was ring"
        | trivial; done; dbg_trace "it was trivial"
        -- | nlinarith; done
        | fail "No, this is not obvious."))


-- Testing of Polynomial
section Polynomial
noncomputable section
#check Polynomial 
#check Polynomial (ℚ)
#check Polynomial.eval


example (f : Polynomial ℚ) (hf : f = Polynomial.C (1 : ℚ)) : Polynomial.eval 2 f = 1 := by
  have : ∀ (q : ℚ), Polynomial.eval q f = 1 := by
    sorry
  obviously

-- example (f : ℤ → ℤ) (hf : ∀ x, f x = x ^ 2) : Polynomial.eval 2 f = 4 := by
--   sorry

-- degree of a constant function is ⊥ (is this same as -1 ???)
#print Polynomial.degree_zero

def F : Polynomial ℚ := Polynomial.C (2 : ℚ)
#print F
#check F
#check Polynomial.degree F
#check Polynomial.degree 0
#check WithBot ℕ
-- #eval Polynomial.degree F
#check Polynomial.eval 1 F
example : Polynomial.eval (100 : ℚ) F = (2 : ℚ) := by
  refine Iff.mpr (Rat.ext_iff (Polynomial.eval 100 F) 2) ?_
  simp only [Rat.ofNat_num, Rat.ofNat_den]
  rw [F]
  simp

-- Treat polynomial f ∈ ℚ[X] as a function f : ℚ → ℚ
#check CoeFun




end section





-- @[BH, 4.1.2]



-- All the polynomials are in ℚ[X], all the functions are considered as ℤ → ℤ
noncomputable section
-- Polynomial type of degree d
@[simp]
def PolyType (f : ℤ → ℤ) (d : ℕ) := ∃ Poly : Polynomial ℚ, ∃ (N : ℤ), (∀ (n : ℤ), N ≤ n → f n = Polynomial.eval (n : ℚ) Poly) ∧ d = Polynomial.degree Poly
section
-- structure PolyType (f : ℤ → ℤ) where
--   Poly : Polynomial ℤ
--   d : 
--   N : ℤ
--   Poly_equal : ∀ n ∈ ℤ → f n = Polynomial.eval n : ℤ Poly

#check PolyType

example (f : ℤ → ℤ) (hf : ∀ x, f x = x ^ 2) : PolyType f 2 := by
  unfold PolyType
  sorry
  -- use Polynomial.monomial (2 : ℤ) (1 : ℤ)
  -- have' := hf 0; ring_nf at this
  -- exact this

end section

-- Δ operator (of d times)
@[simp]
def Δ : (ℤ → ℤ) → ℕ → (ℤ → ℤ)
  | f, 0 => f
  | f, d + 1 => fun (n : ℤ) ↦ (Δ f d) (n + 1) - (Δ f d) (n)  
section
-- def Δ (f : ℤ → ℤ) (d : ℕ) := fun (n : ℤ) ↦ f (n + 1) - f n
-- def add' : ℕ → ℕ → ℕ
--   | 0, m => m 
--   | n+1, m => (add' n m) + 1
-- #eval add' 5 10
#check Δ
def f (n : ℤ) := n
#eval (Δ f 1) 100
-- #check (by (show_term unfold Δ) : Δ f 0=0)
end section






-- (NO need to prove another direction) Constant polynomial function = constant function
lemma Poly_constant (F : Polynomial ℚ) (c : ℚ) : 
  (F = Polynomial.C (c : ℚ)) ↔ (∀ r : ℚ, (Polynomial.eval r F) = (c : ℚ)) := by
  constructor
  · intro h
    rintro r
    refine Iff.mpr (Rat.ext_iff (Polynomial.eval r F) c) ?_
    simp only [Rat.ofNat_num, Rat.ofNat_den]
    rw [h]
    simp
  · sorry




-- Shifting doesn't change the polynomial type
lemma Poly_shifting (f : ℤ → ℤ) (g : ℤ → ℤ) (hf : PolyType f d) (s : ℤ) (hfg : ∀ (n : ℤ), f (n + s) = g (n)) : PolyType g d := by
  simp only [PolyType]
  rcases hf with ⟨F, hh⟩
  rcases hh with ⟨N,ss⟩
  sorry





-- set_option pp.all true in
-- PolyType 0 = constant function
lemma PolyType_0 (f : ℤ → ℤ) : (PolyType f 0) ↔ (∃ (c : ℤ), ∃ (N : ℤ), ∀ (n : ℤ), 
    (N ≤ n → f n = c) ∧ c ≠ 0) := by
  constructor
  · rintro ⟨Poly, ⟨N, ⟨H1, H2⟩⟩⟩ 
    have this1 : Polynomial.degree Poly = 0 := by rw [← H2]; rfl
    have this2 : ∃ (c : ℤ), Poly = Polynomial.C (c : ℚ) := by
      have HH : ∃ (c : ℚ), Poly = Polynomial.C (c : ℚ) := ⟨Poly.coeff 0, Polynomial.eq_C_of_degree_eq_zero (by rw[← H2]; rfl)⟩
      cases' HH with c HHH
      have HHHH : ∃ (d : ℤ), d = c := ⟨f N, by simp [(Poly_constant Poly c).mp HHH N, H1 N (le_refl N)]⟩
      cases' HHHH with d H5; exact ⟨d, by rw[← H5] at HHH; exact HHH⟩
    rcases this2 with ⟨c, hthis2⟩ 
    use c; use N; intro n
    constructor
    · have this4 : Polynomial.eval (n : ℚ) Poly = c := by
        rw [hthis2]; simp only [map_intCast, Polynomial.eval_int_cast]
      exact fun HH1 => Iff.mp (Rat.coe_int_inj (f n) c) (by rw [←this4, H1 n HH1])
    · intro c0
      simp only [hthis2, c0, Int.cast_zero, map_zero, Polynomial.degree_zero] at this1
  · rintro ⟨c, N, hh⟩
    have H2 : (c : ℚ) ≠ 0 := by simp only [ne_eq, Int.cast_eq_zero]; exact (hh 0).2
    exact ⟨Polynomial.C (c : ℚ), N, fun n Nn => by rw [(hh n).1 Nn]; exact (((Poly_constant (Polynomial.C (c : ℚ)) (c : ℚ)).mp rfl) n).symm, by rw [Polynomial.degree_C H2]; rfl⟩

-- Δ of 0 times preserves the function
lemma Δ_0 (f : ℤ → ℤ) : (Δ f 0) = f := by tauto

-- Δ of 1 times decreaes the polynomial type by one
lemma Δ_1 (f : ℤ → ℤ) (d : ℕ): d > 0 → PolyType f d → PolyType (Δ f 1) (d - 1) := by
  sorry


lemma foo (f : ℤ → ℤ) (s : ℕ) : Δ (Δ f 1) s = (Δ f (s + 1)) := by
  sorry





-- Δ of d times maps polynomial of degree d to polynomial of degree 0
lemma foofoo (d : ℕ) : (f : ℤ → ℤ) → (PolyType f d) → (PolyType (Δ f d) 0):= by
  induction' d with d hd
  · intro f h
    rw [Δ_0]
    tauto
  · intro f hf
    have this1 : PolyType f (d + 1) := by tauto
    have this2 : PolyType (Δ f (d + 1)) 0 := by
      have this3 : PolyType (Δ f 1) d := by
        sorry
      clear hf
      specialize hd (Δ f 1)
      have this4 : PolyType (Δ (Δ f 1) d) 0 := by tauto
      rw [foo] at this4
      tauto
    tauto



lemma Δ_d_PolyType_d_to_PolyType_0 (f : ℤ → ℤ) (d : ℕ): PolyType f d → PolyType (Δ f d) 0 := by
  intro h
  have this : ∀ (d : ℕ), ∀ (f :ℤ → ℤ), (PolyType f d) → (PolyType (Δ f d) 0) := by 
    exact foofoo
  specialize this d f
  tauto






-- [BH, 4.1.2] (a) => (b)
-- Δ^d f (n) = c for some nonzero integer c for n >> 0 → f is of polynomial type d
lemma a_to_b (f : ℤ → ℤ) (d : ℕ) : (∃ (c : ℤ), ∃ (N : ℤ), ∀ (n : ℤ), ((N ≤ n → (Δ f d) (n) = c) ∧ c ≠ 0)) → PolyType f d := by
  intro h
  rcases h with ⟨c, N, hh⟩
  have H1 := λ n => (hh n).left
  have H2 := λ n => (hh n).right
  clear hh
  have H2 : c ≠ 0 := by
    tauto
  induction' d with d hd
  -- Base case
  · rw [PolyType_0]
    use c
    use N
    tauto

  -- Induction step
  · sorry



-- [BH, 4.1.2] (a) <= (b)
-- f is of polynomial type d → Δ^d f (n) = c for some nonzero integer c for n >> 0
lemma b_to_a (f : ℤ → ℤ) (d : ℕ) : PolyType f d → (∃ (c : ℤ), ∃ (N : ℤ), ∀ (n : ℤ), ((N ≤ n → (Δ f d) (n) = c) ∧ c ≠ 0)) := by
  intro h
  have : PolyType (Δ f d) 0 := by
    apply Δ_d_PolyType_d_to_PolyType_0
    exact h
  have this1 : (∃ (c : ℤ), ∃ (N : ℤ), ∀ (n : ℤ), ((N ≤ n → (Δ f d) n = c) ∧ c ≠ 0)) := by
    rw [←PolyType_0]
    exact this
  exact this1
end








-- @Additive lemma of length for a SES
-- Given a SES 0 → A → B → C → 0, then length (A) - length (B) + length (C) = 0 
section
-- variable {R M N : Type _} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
--   (f : M →[R] N)
open LinearMap
-- variable {R M : Type _} [CommRing R] [AddCommGroup M] [Module R M]
-- noncomputable def length := Set.chainHeight {M' : Submodule R M | M' < ⊤}


-- Definitiion of the length of a module
noncomputable def length (R M : Type _) [CommRing R] [AddCommGroup M] [Module R M] := Set.chainHeight {M' : Submodule R M | M' < ⊤}
#check length ℤ ℤ
-- #eval length ℤ ℤ


-- @[ext]
-- structure SES (R : Type _) [CommRing R] where
--   A : Type _
--   B : Type _
--   C : Type _
--   f : A →ₗ[R] B
--   g : B →ₗ[R] C
-- left_exact : LinearMap.ker f = 0
-- middle_exact : LinearMap.range f = LinearMap.ker g
-- right_exact : LinearMap.range g = C



-- Definition of a SES (Short Exact Sequence)
-- @[ext]
structure SES {R A B C : Type _} [CommRing R] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [Module R A] [Module R B] [Module R C] 
  (f : A →ₗ[R] B) (g : B →ₗ[R] C)
  where
  left_exact : LinearMap.ker f = ⊥
  middle_exact : LinearMap.range f = LinearMap.ker g
  right_exact : LinearMap.range g = ⊤

#check SES.right_exact
#check SES


-- Additive lemma
lemma length_Additive (R A B C : Type _) [CommRing R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C] 
  (f : A →ₗ[R] B) (g : B →ₗ[R] C)
  : (SES f g) → ((length R A) + (length R C) = (length R B)) := by
  intro h
  rcases h with ⟨left_exact, middle_exact, right_exact⟩
  sorry

end section







