import Mathlib

theorem algebra_14153 {f : ℤ → ℤ} (h1 : ∀ x, f (x + 4) - f x = 8 * x + 20)
    (h2 : ∀ x, f (x ^ 2 - 1) = (f x - x) ^ 2 + x ^ 2 - 2) :
    f 0 = -1 ∧ f 1 = 1 := by
  have eq1 := h2 0
  norm_num at eq1
  have eq2 := h2 (-1)
  norm_num at eq2
  rw [show f (-1) = f 0 ^ 2 - 2 by linarith [eq1]] at eq2
  have eq3 : f 0 * (f 0 ^ 3 - 2 * f 0 - 1) = 0 := by 
    nlinarith
  have eq4 : f 0 = 0 ∨ f 0 ^ 3 - 2 * f 0 - 1 = 0 := by
    cases (mul_eq_zero.mp eq3) with
    | inl h => 
      left; linarith
    | inr h => 
      right; linarith
  cases eq4 with
  | inl h00 =>
    have eq8 : f 0 = 0 := by linarith
    have eq9 : f (-1) = -2 := by 
      rw [eq8] at eq1
      nlinarith
    have eq10 : f 4 = 20 := by
      have eq14 := h1 0
      norm_num at eq14 ⊢
      nlinarith [eq8]
    have eq11 : f 8 = 72 := by
      have eq14 := h1 4
      norm_num at eq14 ⊢
      nlinarith [eq10]
    have eq12 := h2 2
    norm_num at eq12 ⊢
    have eq13 := h2 3
    norm_num at eq13 ⊢
    rw [eq11] at eq13
    -- So $72 = (f 3 - 3) ^ 2 + 7 \implies (f 3 - 3) ^ 2 = 65$.
    have eq14 : (f 3 - 3 : ℤ) ^ 2 = 65 := by 
      nlinarith
    have eq15 : (f 3 - 3 : ℤ) ≤ 8 := by nlinarith [sq_nonneg (f 3 - 3 : ℤ)]
    have eq16 : (f 3 - 3 : ℤ) ≥ -8 := by nlinarith [sq_nonneg (f 3 - 3 : ℤ)]
    interval_cases h : (f 3 - 3 : ℤ) <;> omega
  | inr eq0 =>
    have eq4 : f 0 ^ 3 - 2 * f 0 - 1 = 0 := by linarith
    have eq5 : (f 0 + 1) * (f 0 ^ 2 - f 0 - 1) = 0 := by 
      nlinarith [eq4]
    cases (mul_eq_zero.mp eq5) with
    | inl h => 
      have eq6 : f 0 = -1 := by linarith
      have eq7 : f 1 = 1 := by
        have eq8 := h2 1
        norm_num at eq8 ⊢
        rw [eq6] at eq8
        have eq9 : (f 1 - 1) ^ 2 = 0 := by nlinarith
        have eq10 : f 1 - 1 = 0 := by 
          nlinarith [sq_nonneg (f 1 - 1 : ℤ)]
        linarith
      constructor <;> try linarith
    | inr h => 
      have eq6 : f 0 ^ 2 - f 0 - 1 = 0 := by linarith
      have eq7 : f 0 ≤ 2 := by nlinarith [sq_nonneg (f 0 - 1 : ℤ)]
      have eq8 : f 0 ≥ 0 := by nlinarith [sq_nonneg (f 0 - 1 : ℤ)]
      interval_cases h8 : f 0 <;> omega