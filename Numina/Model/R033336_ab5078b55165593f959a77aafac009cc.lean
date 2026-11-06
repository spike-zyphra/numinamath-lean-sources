import Mathlib

theorem algebra_195653 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x - 2) / y + 5 / (x * y) = (4 - y) / x - abs (y - 2 * x) / (x * y) ↔ x = 1 ∧ y = 2 := by
  constructor
  · -- Assume the equation holds, prove x = 1 and y = 2
    intro h_eq
    have eq2 : x * (x - 2) + 5 = y * (4 - y) - abs (y - 2 * x) := by
      have eq1 : (x - 2) / y + 5 / (x * y) = (4 - y) / x - abs (y - 2 * x) / (x * y) := h_eq
      have h1 : (x - 2) / y + 5 / (x * y) = (x * (x - 2) + 5) / (x * y) := by
        field_simp [hy, show x * y ≠ 0 by
          apply mul_ne_zero 
          exact hx
          exact hy
        ]
        <;> ring
      have h2 : (4 - y) / x - abs (y - 2 * x) / (x * y) = (y * (4 - y) - abs (y - 2 * x)) / (x * y) := by
        field_simp [hx, hy, show x * y ≠ 0 by
            apply mul_ne_zero 
            exact hx
            exact hy
          ]
        <;> ring
      rw [h1, h2] at eq1
      have h4 : x * (x - 2) + 5 = y * (4 - y) - abs (y - 2 * x) := by
        field_simp [hx, hy, show x * y ≠ 0 by
          apply mul_ne_zero 
          exact hx
          exact hy
        ] at eq1 ⊢
        linarith
      linarith
    by_cases h : y - 2 * x ≥ 0
    · -- y - 2 * x ≥ 0
      have h5 : abs (y - 2 * x) = y - 2 * x := by
        rw [abs_of_nonneg h]
      rw [h5] at eq2
      have h6 : (x - 1) ^ 2 + (y - 2) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 2), sq_nonneg (x - y / 2), sq_nonneg (y - 2 * x), sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy]
      have hx1 : x - 1 = 0 := by
        nlinarith
      have hy1 : y - 2 = 0 := by
        nlinarith
      constructor <;> linarith
    · -- y - 2 * x < 0
      have h7 : abs (y - 2 * x) = (2 * x - y) := by
        rw [abs_of_neg (show y - 2 * x < 0 by linarith)]
        all_goals linarith
      rw [h7] at eq2
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 2), sq_nonneg (x - y / 2), sq_nonneg (y - 2 * x), sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy]
  · -- Assume x = 1 and y = 2 prove the equation
    rintro ⟨rfl, rfl⟩
    norm_num [abs_of_nonneg, abs_of_neg, abs_of_pos]