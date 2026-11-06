import Mathlib

theorem algebra_327024 (a : ℝ) (ha : a ≠ 0) (x y : ℤ)
    (h1 : x > 0) (h2 : y > 0) (h3 : x^2 + 2 * a * y = 5) (h4 : y - x = 6 * a) :
    a = 1 / 2 ∨ a = 1 / 6 := by
  have h7 : (a : ℝ) = (y - x) / 6 := by
    have h8 : (y : ℝ) - (x : ℝ) = 6 * a := by 
      exact_mod_cast h4 
    linarith
  have h8 : (x : ℝ)^2 + 2 * ((y - x) / 6) * (y : ℝ) = (5 : ℝ) := by
    rw [h7] at h3 
    linarith
  have h9 : (3 * (x : ℝ)^2 + (y : ℝ)^2 - (x * y : ℝ)) = (15 : ℝ) := by
    have eq5 : (x : ℝ)^2 + 2 * ((y - x) / 6) * (y : ℝ) = (5 : ℝ) := h8
    field_simp at eq5 ⊢ 
    nlinarith
  have eq4 : 3 * x^2 + y^2 - x * y = 15 := by
    exact_mod_cast h9
  have h5 : x ≤ 3 := by 
    nlinarith [sq_nonneg (y - 2 * x), sq_nonneg (y - 4), sq_nonneg (x - 1), sq_nonneg (x - 2)]
  have h6 : x = 1 ∨ x = 2 := by 
    have h5' : x ≤ 3 := h5 
    have h1' : x > 0 := h1
    interval_cases x <;> try { 
      omega 
    } <;> try { 
      exfalso 
      have : 3 * 3 ^ 2 + y ^ 2 - 3 * y = 15 := eq4 
      have h14 : y ^ 2 - 3 * y + 12 = 0 := by 
        nlinarith 
      have h12 : y ≤ 8 := by 
        nlinarith [sq_nonneg (y * 1 : ℤ), sq_nonneg ((y - 3 * 1) : ℤ)]
      have h12 : y ≥ 1 := by omega 
      have h13 : y ≤ 5 := by 
        nlinarith [sq_nonneg (y - 3 : ℤ), sq_nonneg (y * 1 : ℤ)]
      interval_cases y <;> omega 
    }
  cases h6 with 
  | inl hx1 =>
    have hx1' : x = 1 := hx1 
    have hy : y = 4 := by 
      rw [show x = 1 by linarith [hx1']] at eq4 
      nlinarith 
    have h6' : (a : ℝ) = (1 / 2 : ℝ) := by 
      rw [show (y : ℝ) = 4 by exact_mod_cast hy, show (x : ℝ) = 1 by exact_mod_cast hx1'] at h7 
      nlinarith 
    left 
    linarith 
  | inr hx1 =>
    have hx1' : x = 2 := hx1 
    have hy : y = 3 := by 
      rw [show x = 2 by linarith [hx1']] at eq4 
      nlinarith 
    have h6' : (a : ℝ) = (1 / 6 : ℝ) := by 
      rw [show (y : ℝ) = 3 by exact_mod_cast hy, show (x : ℝ) = 2 by exact_mod_cast hx1'] at h7 
      nlinarith 
    right 
    linarith