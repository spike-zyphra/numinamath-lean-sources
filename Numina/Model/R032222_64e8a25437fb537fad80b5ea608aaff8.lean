import Mathlib

theorem algebra_129211 {P : Polynomial ℝ} (hP : ∀ n, P.coeff n = 1 ∨ P.coeff n = -1)
    (hroots : ∀ r ∈ P.roots, ∃ x : ℝ, r = x) :
    P = X + 1 ∨ P = -(X + 1) ∨ P = X - 1 ∨ P = -(X - 1) ∨
    P = X ^ 2 + X - 1 ∨ P = -(X ^ 2 + X - 1) ∨
    P = X ^ 2 - X - 1 ∨ P = -(X ^ 2 - X - 1) ∨
    P = X ^ 3 + X ^ 2 - X - 1 ∨ P = -(X ^ 3 + X ^ 2 - X - 1) ∨
    P = X ^ 3 - X ^ 2 - X + 1 ∨ P = -(X ^ 3 - X ^ 2 - X + 1) := by 
  have h3 := hP (P.natDegree + 1)
  -- For finite polynomial P, the coefficient at degree P.natDegree + 1 is zero. But the hypothesis says it's ±1
  have h0 : P.coeff (P.natDegree + 1) = 0 := by
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    linarith
  cases h3 with
  | inl h1 => 
    rw [h0] at h1
    norm_num at h1
  | inr h1 => 
    rw [h0] at h1
    norm_num at h1