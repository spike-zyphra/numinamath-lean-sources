import Mathlib

theorem algebra_10398 :
    IsGreatest {z : ℝ | ∃ x y, z = x + 2 * y - 1 / x ∧ x - y ≤ 0 ∧ 4 * x - y ≥ 0 ∧ x + y ≤ 3} 4 := by
  constructor
  · -- Show 4 is in the set.
    use 1, 2
    norm_num
  · -- Show 4 is greatest
    intro z h
    rcases h with ⟨x, y, h_eq, h1, h2, h3⟩
    -- Show that $z \leq 4$
    have h4 : x ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (4 * x - y), sq_nonneg (x + y - 3)]
    by_cases hx : x > 0
    · -- Case where $x > 0$
      -- Show that $x + 2y - 1/x \leq 4$
      -- Since x > 0, multiply both sides by x to get $x^2 + 2xy - 4x -1 \leq 0$
      have h7 : x + 2 * y - 1 / x - 4 ≤ 0 := by
        have h11 : x + 2 * y - 1 / x - 4 = (x^2 + 2 * x * y - 4 * x - 1) / x := by
          field_simp
          ring 
        rw [h11] at *
        -- Show that $x^2 + 2xy - 4x -1 \leq 0$
        have h12 : x ^ 2 + 2 * x * y - 4 * x - 1 ≤ 0 := by 
          nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 2), sq_nonneg (y - x), sq_nonneg (y - 4 * x), sq_nonneg (x + y - 3), mul_nonneg (show 0 ≤ (4 : ℝ) by norm_num) (show 0 ≤ (4 : ℝ) by norm_num)]
        -- Divide by positive x
        have h13 : (x ^ 2 + 2 * x * y - 4 * x - 1) / x ≤ 0 := by 
          apply div_nonpos_of_nonpos_of_nonneg 
          linarith 
          linarith 
        linarith 
      -- From inequality, rewrite h_eq
      have h8 : x + 2 * y - 1 / x ≤ 4 := by linarith 
      -- Use h_eq to conclude z <= 4
      linarith [h_eq, h8]
    · -- Case where $x \le 0$
      -- Since $x \ge 0$ from previous proof, this means $x = 0$.
      have hx0 : x = 0 := by
        linarith 
      -- From constraints at x=0:
      -- h1: x - y <= 0 => 0 - y <= 0 => y >= 0
      -- h2: 4x - y >= 0 => 0 - y >= 0 => y <= 0
      -- Thus y = 0.
      have hy0 : y = 0 := by
        have h1' : y ≥ 0 := by 
          nlinarith 
        have h2' : y ≤ 0 := by 
          nlinarith 
        linarith 
      -- Use h_eq to rewrite z and conclude z <= 4
      rw [hx0, hy0] at h_eq
      rw [h_eq]
      norm_num
      all_goals try { linarith }