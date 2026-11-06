import Mathlib

theorem algebra_267627 (a b c : ℝ) (h₀ : Real.logb 10 0.021 = 2 * a + b + c - 3)
    (h₁ : Real.logb 10 0.27 = 6 * a - 3 * b - 2) (h₂ : Real.logb 10 1.5 = 3 * a - b + c)
    (h₃ : Real.logb 10 2.8 = 1 - 2 * a + 2 * b - c) (h₄ : Real.logb 10 3 = 2 * a - b)
    (h₅ : Real.logb 10 5 = a + c) (h₆ : Real.logb 10 6 = 1 + a - b - c) (h₇ : Real.logb 10 7 = 2 * b + 2 * c)
    (h₈ : Real.logb 10 8 = 3 - 3 * a - 3 * c) (h₉ : Real.logb 10 9 = 4 * a - 2 * b)
    (h₁₀ : Real.logb 10 14 = 1 - a + 2 * b) :
    Real.logb 10 1.5 = 3 - b - 1 ∧ Real.logb 10 7 = 2 * b + 2 * c := by

  have h15 : Real.logb 10 1.5 = Real.logb 10 3 - Real.logb 10 2 := by
    have h151 : Real.logb 10 1.5 = Real.logb 10 (3 / 2 : ℝ) := by norm_num
    rw [h151]
    have h152 : Real.logb 10 (3 / 2 : ℝ) = Real.logb 10 3 - Real.logb 10 2 := by 
      field_simp [Real.logb_div]
    rw [h152]

  have h153 : Real.logb 10 3 = 2 * a - b := by linarith [h₄]

  have h154 : Real.logb 10 2 = 1 - a - c := by 
    have h1541 : Real.logb 10 2 + Real.logb 10 5 = 1 := by 
      have h21 : Real.logb 10 2 + Real.logb 10 5 = Real.logb 10 (2 * 5 : ℝ) := by 
        rw [Real.logb_mul (by norm_num) (by norm_num)]
      have h22 : Real.logb 10 (2 * 5 : ℝ) = Real.logb 10 10 := by norm_num
      have h23 : Real.logb 10 10 = 1 := Real.logb_self_eq_one (by norm_num)
      linarith [h21, h22, h23]
    have h1542 : Real.logb 10 5 = a + c := by linarith [h₅]
    linarith [h1541, h1542]

  have h155 : Real.logb 10 1.5 = 3 * a - b + c - 1 := by
    rw [h15, h153, h154]
    linarith

  have h16 : a + c = 1 := by
    nlinarith [h₁₀, h₃, h₅, h₇, h₉]

  have h3 : Real.logb 10 1.5 = 3 - b - 1 := by
    nlinarith [h155, h16]

  have h4 : Real.logb 10 7 = 2 * b + 2 * c := by
    linarith [h₇]

  exact ⟨h3, h4⟩