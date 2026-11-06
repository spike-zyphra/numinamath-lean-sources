import Mathlib

theorem algebra_187477 (x : ℝ) : 3 * (9 : ℝ) ^ x + 2 * (3 : ℝ) ^ x = 1 ↔ x = -1 := by
    constructor
    · -- Forward direction: if $3 \cdot 9^{x}+2 \cdot 3^{x}=1$ then $x = -1$
      intro h
      have h1 : (9 : ℝ) ^ x = (3 : ℝ) ^ (2 * x) := by -- Rewrite $9^x$ as $3^{2x}$
          rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num]
          rw [← Real.rpow_mul]
          ring
          all_goals linarith
      rw [h1] at h
      have h2 : (3 : ℝ) ^ (2 * x) = ((3 : ℝ) ^ x) ^ 2 := by -- Simplify $3^{2x}$ to $(3^x)^2$
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals linarith
      rw [h2] at h
      have h3 : 3 * ((3 : ℝ) ^ x) ^ 2 + 2 * (3 : ℝ) ^ x - 1 = 0 := by -- Rearrange to form quadratic equation
          linarith
      have h4 : (3 : ℝ) ^ x > 0 := by -- Verify $3^x > 0$ (positive real power result)
          apply Real.rpow_pos_of_pos
          norm_num
      have h5 : ((3 : ℝ) ^ x - 1 / 3) * ((3 : ℝ) ^ x + 1) = 0 := by -- Factor quadratic equation
          nlinarith [h3]
      cases' (mul_eq_zero.mp h5) with h6 h7 -- Case analysis for each factor
      · -- Case 1: $3^x - 1/3 = 0$, so $3^x = 1/3$
        have h8 : (3 : ℝ) ^ x = 1 / 3 := by
            linarith
        have h9 : x = -1 := by -- Take logarithm base 3 of both sides to solve for x
            apply_fun (Real.logb (3 : ℝ)) at h8
            simp at h8
            linarith
        exact h9
      · -- Case 2: $3^x + 1 = 0$, so $3^x = -1$ (impossible since $3^x > 0$)
        have h8 : (3 : ℝ) ^ x = -1 := by
            linarith
        linarith [h4, h8] -- Contradiction
    · -- Backward direction: if x = -1, then $3 \cdot 9^x + 2 \cdot 3^x = 1$
      intro h
      rw [h] -- Substitute x = -1 into the equation
      norm_num -- Lean verifies the arithmetic is correct