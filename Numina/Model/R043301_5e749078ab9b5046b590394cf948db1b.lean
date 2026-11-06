import Mathlib

theorem algebra_1038 {x y : ℝ} (h₀ : abs (x - y) + abs x = 5) (h₁ : 2 * abs (x - y) + 3 * abs x = 13) :
    abs x + abs y = 4 ∨ abs x + abs y = 8 := by 
  have eq1 : abs (x - y) = 5 - abs x := by linarith
  have eq2 : 2 * (5 - abs x) + 3 * abs x = 13 := by 
    rw [eq1] at h₁
    linarith
  have hx1 : abs x = 3 := by 
    linarith 
  have h2 : abs (x - y) = 2 := by 
    rw [hx1] at eq1 
    linarith 
  have h4 : x = 3 ∨ x = -3 := by 
    cases eq_or_eq_neg_of_abs_eq hx1 with 
    | inl h4 =>
      left 
      linarith 
    | inr h4 =>
      right 
      linarith 
  cases h4 with
  | inl hx2 =>
    have h5 : abs (x - y) = 2 := h2
    rw [show x - y = (3 : ℝ) - y by 
      rw [hx2]
    ] at h5 
    have h6 : abs ((3 : ℝ) - y) = 2 := h5
    cases eq_or_eq_neg_of_abs_eq h6 with
    | inl h7 =>
      have hy1 : y = 1 := by linarith 
      have h : abs x + abs y = 4 := by 
        rw [hx1] 
        rw [show abs y = 1 by 
          rw [hy1] 
          norm_num 
        ] 
        all_goals norm_num 
      left 
      linarith 
    | inr h7 =>
      have hy2 : y = 5 := by linarith 
      have h : abs x + abs y = 8 := by 
        rw [hx1] 
        rw [show abs y = 5 by 
          rw [hy2] 
          norm_num 
        ] 
        all_goals norm_num 
      right 
      linarith 
  | inr hx2 =>
    have h5 : abs (x - y) = 2 := h2 
    rw [show x - y = (-3 : ℝ) - y by 
      rw [hx2] 
    ] at h5 
    have h6 : abs ((-3 : ℝ) - y) = 2 := h5
    cases eq_or_eq_neg_of_abs_eq h6 with 
    | inl h7 =>
      have hy1 : y = -5 := by linarith 
      have h : abs x + abs y = 8 := by 
        rw [hx1] 
        rw [show abs y = 5 by 
          rw [hy1] 
          norm_num [abs_of_nonneg, abs_of_nonpos]
        ] 
        all_goals norm_num 
      right 
      linarith 
    | inr h7 =>
      have hy2 : y = -1 := by linarith 
      have h : abs x + abs y = 4 := by 
        rw [hx1] 
        rw [show abs y = 1 by 
          rw [hy2] 
          norm_num 
        ] 
        all_goals norm_num 
      left 
      linarith