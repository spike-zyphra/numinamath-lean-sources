import Mathlib

theorem algebra_167470 {f : ℝ → ℝ} (h₁ : ∀ x, |f x| ≥ 1)
    (h₂ : ∀ x y, f (x + y) = (f x + f y) / (1 + f x * f y)) :
    ∀ x, f x = 1 ∨ f x = -1 := by
  have h4 : f 0 ≠ 0 := by
    by_contra h11
    have h8 : f 0 = 0 := by nlinarith
    have h9 : |f 0| < (1 : ℝ) := by
      rw [h8]
      norm_num
    have h10 : |f 0| ≥ (1 : ℝ) := h₁ 0
    linarith [abs_nonneg (f 0), h9, h10]

  have h12 : ∀ x : ℝ, f x ^ 2 = 1 := by
    intro x
    have h10 := h₂ x 0
    have eq1 : f x = (f x + f 0) / (1 + f x * f 0) := by
      simp at h10 ⊢
      all_goals
      linarith
    by_cases h13 : (1 + f x * f 0) = 0
    · -- If $1 + f x * f 0 = 0$, then $f x * f 0 = -1$.
      have eq2 : f x * f 0 = -1 := by linarith
      have h14 : f x ≠ 0 := by
        by_contra h15
        have h16 : f x = 0 := by nlinarith
        rw [h16] at eq2
        nlinarith
      have h8 : |f 0| ≥ (1 : ℝ) := h₁ 0
      have eq3 : f 0 = -1 / f x := by
        field_simp [h14]
        all_goals
        nlinarith
      have h9 : |f 0| = 1 / |f x| := by
        rw [eq3]
        have h4 : |(-1 / f x : ℝ)| = 1 / |f x| := by
          have h100 : f x ≠ 0 := by
            by_contra h101
            have h102 : f x = 0 := by nlinarith
            contradiction
          simp [abs_div, abs_of_pos (show (0 : ℝ) < (1 : ℝ) by norm_num), abs_neg, h100]
          all_goals 
            try { nlinarith } 
        linarith [h4]
      have h14 : |f x| ≥ (1 : ℝ) := h₁ x
      have h11 : |f x| ≤ (1 : ℝ) := by
        have h12 : 1 / |f x| ≥ (1 : ℝ) := by 
          linarith [h8, h9]
        have h4' : |f x| > 0 := by
          have h16 : |f x| ≥ (1 : ℝ) := h₁ x
          nlinarith [abs_nonneg (f x)]
        have h16 : |f x| ≤ (1 : ℝ) := by
          have h5' : |f x| > 0 := h4'
          have h6' : (1 / |f x|) * |f x| ≥ (1 : ℝ) * |f x| := by 
            apply mul_le_mul_of_nonneg_right 
            all_goals
              nlinarith 
          have h10 : (1 / |f x|) * |f x| = 1 := by 
            field_simp [h4']
          nlinarith [h10, h6', abs_nonneg (f x)]
        linarith 
      have h16 : |f x| = (1 : ℝ) := by 
        linarith [h14, h11]
      have h17 : f x ^ 2 =1 := by
        cases' abs_cases (f x) with h18 h18
        all_goals
          nlinarith
      assumption
    · -- $1 + f x * f 0 ≠ 0$.
      have eq3 : f x * (1 + f x * f 0) = f x + f 0 := by
        have eq5 : f x = (f x + f 0) / (1 + f x * f 0) := by
          linarith [eq1]
        field_simp [h13] at eq5 ⊢
        all_goals
          nlinarith 
      have eq4 : f x ^ 2 * f 0 = f 0 := by
        linarith 
      have eq5 : f x ^ 2 = 1 := by 
        have eq6 : (f x ^ 2 - 1) * f 0 = 0 := by 
          linarith
        cases (mul_eq_zero.1 eq6) with
        | inl h16 => 
          linarith 
        | inr h15 => 
          exfalso 
          apply h4
          linarith 
      assumption

  intro x
  have h66 : f x ^ 2 = 1 := h12 x
  have h67 : f x = 1 ∨ f x = -1 := by 
    have h70 : f x ^ 2 - 1 = 0 := by
      linarith 
    have h71 : (f x - 1) * (f x + 1) = 0 := by 
      nlinarith 
    cases (mul_eq_zero.1 h71) with 
    | inl h13 =>
      left 
      linarith 
    | inr h13 =>
      right 
      linarith 
  assumption