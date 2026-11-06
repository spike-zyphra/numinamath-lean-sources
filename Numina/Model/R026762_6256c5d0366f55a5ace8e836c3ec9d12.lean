import Mathlib

theorem algebra_312086 (a : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = 4 * x ^ 2 - 4 * a * x + (a ^ 2 - 2 * a) + 2)
    (h₁ : ∃ x ∈ Set.Icc 0 1, f x = 2)
    (h₂ : ∀ x ∈ Set.Icc 0 1, f x ≥ 2) :
    a = 0 ∨ a = 3 + Real.sqrt 5 := by
  rcases h₁ with ⟨x, hx, hfx⟩
  have h0_le_x : 0 ≤ x := by
    have h1 : x ∈ Set.Icc 0 1 := hx
    exact h1.1
  have hx_le_1 : x ≤ 1 := by
    have h1 : x ∈ Set.Icc 0 1 := hx
    exact h1.2
  have h3 : f x = 2 := hfx
  rw [h₀] at h3
  have h3' : 4 * x ^ 2 - 4 * a * x + (a ^ 2 - 2 * a) + 2 = 2 := by 
    linarith
  have eq1 : 4 * x ^ 2 - 4 * a * x + (a ^ 2 - 2 * a) = 0 := by
    nlinarith
  have h4 : (2 * x - a) ^ 2 = 2 * a := by
    nlinarith
  have h5 : 2 * a ≥ 0 := by
    nlinarith [sq_nonneg (2 * x - a), h4]
  have h8 : a ≥ 0 := by nlinarith
  have h6 : f 0 ≥ 2 := by
    apply h₂ 
    exact ⟨by norm_num, by norm_num⟩
  have h7 : f 1 ≥ 2 := by 
    apply h₂ 
    exact ⟨by norm_num, by norm_num⟩
  simp [h₀] at h6 h7
  -- h6 expands to a^2 -2*a +2 ≥ 2 → a^2 -2*a ≥ 0
  -- h7 expands to a^2 -6*a +6 ≥ 2 →a^2 -6*a +4 ≥0
  have hfx0 : a * (a - 2) ≥ 0 := by nlinarith
  have hfx1 : a ^ 2 - 6 * a + 4 ≥ 0 := by nlinarith
  -- Solving the quadratic equations
  by_cases h : a ≤ 2
  · -- Assume that a ≤ 2, solve the equations using endpoints
    have hx1 : a = 0 := by
      nlinarith [sq_nonneg (a - 0), sq_nonneg (x), sq_nonneg (x - 0.5), sq_nonneg (x - 1)]
    left
    exact hx1
  · -- Case where a > 2
    have ha1 : a > 2 := by 
      nlinarith
    -- Solving equations using endpoints
    have ha2 : a = 3 + Real.sqrt 5 := by 
      nlinarith [sq_nonneg (a - (3 + Real.sqrt 5)), sq_nonneg (x - 1), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    right
    linarith