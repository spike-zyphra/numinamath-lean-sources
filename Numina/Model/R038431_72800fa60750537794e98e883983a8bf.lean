import Mathlib

theorem algebra_174637 {a b : ℝ} (hab : a * b * (a + b) = 1) :
    a / (a ^ 3 + a + 1) = b / (b ^ 3 + b + 1) := by

  have h4 : a * (b ^ 3 + b + 1) = b * (a ^ 3 + a + 1) := by
    have h5 : a * (b ^ 3 + b + 1) - b * (a ^ 3 + a + 1) = 0 := by
      have h6 : a * (b ^ 3 + b + 1) - b * (a ^ 3 + a + 1) = (a - b) * (1 - a * b * (a + b)) := by
        ring
      rw [h6]
      have h7 : a * b * (a + b) = 1 := hab
      have h8 : 1 - a * b * (a + b) = 0 := by
        linarith [h7]
      rw [h8]
      norm_num
    linarith

  have h5 : a / (a ^ 3 + a + 1) = b / (b ^ 3 + b + 1) := by
    have h6 : (a / (a ^ 3 + a + 1) - b / (b ^ 3 + b + 1)) = 0 := by
      have h7 : a / (a ^ 3 + a + 1) - b / (b ^ 3 + b + 1) = (a * (b ^ 3 + b + 1) - b * (a ^ 3 + a + 1)) / ((a ^ 3 + a + 1) * (b ^ 3 + b + 1)) := by
        field_simp [(show a ^ 3 + a + 1 ≠ 0 from by
          by_contra h
          have h1 : a ^ 3 + a + 1 = 0 := h
          have h2 : a * (a ^ 2 + 1) = -1 := by
            nlinarith
          nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a * b), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), sq_nonneg ((a + b) ^ 2)]
        ), (show b ^ 3 + b + 1 ≠ 0 from by
          by_contra h
          have h1 : b ^ 3 + b + 1 = 0 := h
          have h2 : b * (b ^ 2 + 1) = -1 := by
            nlinarith
          nlinarith [sq_nonneg (b ^ 2), sq_nonneg (a * b), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), sq_nonneg ((a + b) ^ 2)]
        )
        ]
        <;> ring
      rw [h7]
      have h8 : a * (b ^ 3 + b + 1) - b * (a ^ 3 + a + 1) = 0 := by
        linarith [h4]
      rw [h8]
      norm_num
    linarith
  exact h5