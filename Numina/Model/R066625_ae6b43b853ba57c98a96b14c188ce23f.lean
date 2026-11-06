import Mathlib

/- The solution to the equation $\sqrt{\left| x+y \right|-5}+\sqrt{y+18}=0$ is ___          ___ or ___          ___. -/
theorem algebra_2765 (x y : ℝ) : (|x + y| - 5 ≥ 0 ∧ y + 18 ≥ 0 ∧ √(|x + y| - 5) + √(y + 18) = 0) ↔
    (x = 13 ∧ y = -18) ∨ (x = 23 ∧ y = -18) := by
  constructor
  · -- First, we verify that if constraint holds, solutions will be y = -18 and x = 13/23.
    intro h
    rcases h with ⟨h1, h2, h_eq⟩
    have h2_eq : √(|x + y| - 5) = 0 := by
      linarith [Real.sqrt_nonneg (|x + y| - 5), Real.sqrt_nonneg (y + 18), h_eq]
    have h3_eq : √(y + 18) = 0 := by 
      linarith [Real.sqrt_nonneg (|x + y| - 5), Real.sqrt_nonneg (y + 18), h_eq]
    have h4 : |x + y| - 5 = 0 := by
      rw [Real.sqrt_eq_zero (by linarith)] at h2_eq
      linarith
    have h5 : y + 18 = 0 := by
      rw [Real.sqrt_eq_zero (by linarith)] at h3_eq
      linarith
    have hy : y = -18 := by linarith
    have h6 : |x + y| = 5 := by
      linarith [h4]
    rw [show x + y = x + (-18) by rw [hy]] at h6
    cases eq_or_eq_neg_of_abs_eq h6 with
    | inl h7 =>
      have hx : x = 23 := by linarith
      right
      constructor
      · linarith
      · linarith
    | inr h8 =>
      have hx : x = 13 := by linarith
      left
      constructor
      · linarith
      · linarith
  · -- Assume either ((13, -18)) or ((23, -18)), verify constraints
    rintro (h | h)
    · -- Case 1, x = 13, y = -18
      rcases h with ⟨hx, hy⟩
      constructor
      · -- Show |x + y| - 5 ≥ 0
        rw [show x + y = (13 + -18 : ℝ) by rw [hx, hy]]
        norm_num [abs_of_nonneg]
      constructor
      · -- Show y + 18 ≥ 0
        rw [hy]
        norm_num
      · -- Show √(|x + y| - 5) + √(y + 18) = 0
        rw [show x + y = (13 + -18 : ℝ) by rw [hx, hy]]
        rw [show y + 18 = (-18 + 18 : ℝ) by rw [hy]]
        have h1 : |(13 + -18 : ℝ)| = 5 := by norm_num [abs_of_nonneg]
        have h2 : |(13 + -18 : ℝ)| - 5 = 0 := by linarith [h1]
        have h3 : √(|(13 + -18 : ℝ)| - 5) = 0 := by
          rw [show |(13 + -18 : ℝ)| - 5 = (0 : ℝ) by linarith [h2]]
          simp
        have h4 : (-18 + 18 : ℝ) = 0 := by linarith
        have h5 : √((-18 + 18 : ℝ)) = 0 := by
          rw [show (-18 + 18 : ℝ) = (0 : ℝ) by linarith [h4]]
          simp
        linarith [h3, h5]
    · -- Case 2, x = 23, y = -18
      rcases h with ⟨hx, hy⟩
      constructor
      · -- Show |x + y| - 5 ≥ 0
        rw [show x + y = (23 + -18 : ℝ) by rw [hx, hy]]
        norm_num [abs_of_nonneg]
      constructor
      · -- Show y + 18 ≥ 0
        rw [hy]
        norm_num
      · -- Show √(|x + y| - 5) + √(y + 18) = 0
        rw [show x + y = (23 + -18 : ℝ) by rw [hx, hy]]
        rw [show y + 18 = (-18 + 18 : ℝ) by rw [hy]]
        have h1 : |(23 + -18 : ℝ)| = 5 := by norm_num [abs_of_nonneg]
        have h2 : |(23 + -18 : ℝ)| - 5 = 0 := by linarith [h1]
        have h3 : √(|(23 + -18 : ℝ)| - 5) = 0 := by
          rw [show |(23 + -18 : ℝ)| - 5 = (0 : ℝ) by linarith [h2]]
          simp
        have h4 : (-18 + 18 : ℝ) = 0 := by linarith
        have h5 : √((-18 + 18 : ℝ)) = 0 := by
          rw [show (-18 + 18 : ℝ) = (0 : ℝ) by linarith [h4]]
          simp
        linarith [h3, h5]