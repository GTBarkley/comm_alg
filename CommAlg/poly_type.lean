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
variable [Semiring ℕ]
variable [Semiring ℤ]
variable [Semiring ℚ]
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
def PolyType (f : ℤ → ℤ) (d : ℕ) := ∃ Poly : Polynomial ℚ, ∃ (N : ℤ), ∀ (n : ℤ), N ≤ n → f n = Polynomial.eval (n : ℚ) Poly ∧ d = Polynomial.degree Poly
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


-- (NO need to prove) Constant polynomial function = constant function
lemma Poly_constant (F : Polynomial ℚ) (c : ℚ) : 
  (F = Polynomial.C c) ↔ (∀ r : ℚ, (Polynomial.eval r F) = c) := by
  constructor
  · intro h
    rintro r
    refine Iff.mpr (Rat.ext_iff (Polynomial.eval r F) c) ?_
    simp only [Rat.ofNat_num, Rat.ofNat_den]
    rw [h]
    simp
  · sorry

-- PolyType 0 = constant function
lemma PolyType_0 (f : ℤ → ℤ) : (PolyType f 0) ↔ (∃ (c : ℤ), ∃ (N : ℤ), ∀ (n : ℤ), (N ≤ n → f n = c) ∧ c ≠ 0) := by
  constructor
  · intro h
    rcases h with ⟨Poly, hN⟩
    rcases hN with ⟨N, hh⟩
    have H1 := λ n hn => (hh n hn).left
    have H2 := λ n hn => (hh n hn).right
    clear hh
    specialize H2 (N + 1)
    have this1 : Polynomial.degree Poly = 0 := by
      have : N ≤ N + 1 := by
        dsimp
        simp
      tauto
    have this2 : ∃ (c : ℤ), Poly = Polynomial.C (c : ℚ) := by
      have HH : ∃ (c : ℚ), Poly = Polynomial.C (c : ℚ) := by
        use Poly.coeff 0
        apply Polynomial.eq_C_of_degree_eq_zero
        exact this1
      cases' HH with c HHH
      have HHHH : ∃ (d : ℤ), d = c := by
        sorry
      cases' HHHH with d H5
      use d
      rw [H5]
      exact HHH
    clear this1
    rcases this2 with ⟨c, hthis2⟩
    use c
    use N
    intro n
    specialize H1 n
    constructor
    · intro HH1
      have this3 : f n = Polynomial.eval (n : ℚ) Poly := by
        tauto
      have this4 : Polynomial.eval (n : ℚ) Poly = c := by
        rw [hthis2]
        dsimp
        simp
      have this5 : f n = (c : ℚ) := by
        rw [←this4, this3]
      exact Iff.mp (Rat.coe_int_inj (f n) c) this5
    · sorry


  · intro h
    rcases h with ⟨c, N, aaa⟩
    let (Poly : Polynomial ℚ) := Polynomial.C (c : ℚ)
    use Poly
    use N
    intro n Nn
    specialize aaa n
    have this1 : c ≠ 0 →  f n = c := by
      tauto
    constructor
    · sorry
    · sorry
      -- apply Polynomial.degree_C c

-- Δ of d times maps polynomial of degree d to polynomial of degree 0
lemma Δ_PolyType_d_to_PolyType_0 (f : ℤ → ℤ) (d : ℕ): PolyType f d → PolyType (Δ f d) 0 := by
  intro h
  rcases h with ⟨Poly, hN⟩
  rcases hN with ⟨N, hh⟩
  have H1 := λ n hn => (hh n hn).left
  have H2 := λ n hn => (hh n hn).right
  clear hh
  have HH2 : d = Polynomial.degree Poly := by
    sorry
  induction' d with d hd
  · rw [PolyType_0]
    sorry
  · sorry

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
  · rw [PolyType_0]
    use c
    use N
    tauto
  · sorry

-- [BH, 4.1.2] (a) <= (b)
-- f is of polynomial type d → Δ^d f (n) = c for some nonzero integer c for n >> 0
lemma b_to_a (f : ℤ → ℤ) (d : ℕ) : PolyType f d → (∃ (c : ℤ), ∃ (N : ℤ), ∀ (n : ℤ), ((N ≤ n → (Δ f d) (n) = c) ∧ c ≠ 0)) := by
  intro h
  have : PolyType (Δ f d) 0 := by
    apply Δ_PolyType_d_to_PolyType_0
    exact h
  have this1 : (∃ (c : ℤ), ∃ (N : ℤ), ∀ (n : ℤ), ((N ≤ n → (Δ f d) n = c) ∧ c ≠ 0)) := by
    rw [←PolyType_0]
    exact this
  exact this1
end

-- @Additive lemma of length for a SES
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
