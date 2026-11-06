import Mathlib

theorem inequalities_291968 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * b * c * d = 1) :
    1 / (a + b + 2) + 1 / (b + c + 2) + 1 / (c + d + 2) + 1 / (d + a + 2) ≤ 1 := by 
  have h1 : ∀ x y : ℝ, x > 0 → y > 0 → x + y ≥ 2 * Real.sqrt (x * y) := by
    intros x y hx hy
    have h1 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
      rw [Real.sqrt_mul]
      all_goals linarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y]
    nlinarith [sq_nonneg (x - y), sq_nonneg (Real.sqrt x - Real.sqrt y), 
      Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith),
      h1, Real.sqrt_nonneg (x * y)]
  
  have h2 : ∀ x y : ℝ, x > 0 → y > 0 → 1 / (x + y + 2) ≤ 1 / (2 * Real.sqrt (x * y) + 2) := by 
    intro x y hx hy
    have h3 : x + y ≥ 2 * Real.sqrt (x * y) := h1 x y hx hy
    have h4 : x + y + 2 ≥ 2 * Real.sqrt (x * y) + 2 := by linarith
    have h5 : 0 < 2 * Real.sqrt (x * y) + 2 := by nlinarith [Real.sqrt_nonneg (x * y), Real.sq_sqrt (show 0 ≤ (x * y : ℝ) by positivity)]
    have h6 : 0 < x + y + 2 := by nlinarith
    have h7 : 1 / (x + y + 2) ≤ 1 / (2 * Real.sqrt (x * y) + 2) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    exact h7
  
  have h3 := h2 a b ha hb
  have h4 := h2 b c hb hc
  have h5 := h2 c d hc hd
  have h6 := h2 d a hd ha
  
  have h7 : a * b * c * d = 1 := h
  
  have hcd : Real.sqrt (c * d) = 1 / Real.sqrt (a * b) := by
    have hcd : c * d = 1 / (a * b) := by 
      field_simp
      nlinarith [h]
    rw [hcd]
    field_simp
    <;> rw [Real.sqrt_div]
    <;> rw [Real.sqrt_eq_zero]
    all_goals positivity
  
  have hbc : Real.sqrt (b * c) = 1 / Real.sqrt (d * a) := by 
    have hbc : b * c = 1 / (d * a) := by 
      field_simp
      nlinarith [h]
    rw [hbc]
    field_simp
    <;> rw [Real.sqrt_div]
    <;> rw [Real.sqrt_eq_zero]
    all_goals positivity
  
  have h9 : 1 / (2 * Real.sqrt (a * b) + 2) + 1 / (2 * Real.sqrt (c * d) + 2) = 1 / 2 := by
    rw [hcd]
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < a * b by positivity), Real.sq_sqrt (show 0 ≤ (a * b : ℝ) by positivity)]
  
  have h10 : 1 / (2 * Real.sqrt (b * c) + 2) + 1 / (2 * Real.sqrt (d * a) + 2) = 1 / 2 := by
    rw [hbc]
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < b * c by positivity), Real.sq_sqrt (show 0 ≤ (b * c : ℝ) by positivity)]
  
  have h12 : 1 / (a + b + 2) + 1 / (c + d + 2) ≤ 1 / 2 := by 
    have h14 : 1 / (a + b + 2) ≤ 1 / (2 * Real.sqrt (a * b) + 2) := h3
    have h15 : 1 / (c + d + 2) ≤ 1 / (2 * Real.sqrt (c * d) + 2) := h5
    linarith [h14, h15, h9]
  
  have h17 : 1 / (b + c + 2) + 1 / (d + a + 2) ≤ 1 / 2 := by 
    have h18 : 1 / (b + c + 2) ≤ 1 / (2 * Real.sqrt (b * c) + 2) := h4
    have h19 : 1 / (d + a + 2) ≤ 1 / (2 * Real.sqrt (d * a) + 2) := h6
    linarith [h18, h19, h10]
  
  linarith [h12, h17]