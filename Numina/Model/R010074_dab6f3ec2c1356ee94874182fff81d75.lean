import Mathlib
open Real Set

theorem algebra_9159 : IsGreatest
  {z | ∃ x y, x > 0 ∧ y > 0 ∧ 2*x + y = 20 ∧ z = logb 10 x + logb 10 y} (2 - logb 10 2) := by
  constructor
  · -- Show $2 - \logb 10 2$ is in the set
    use 5, 10
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    -- Compute z
    have h1 : logb 10 10 = 1 := by
      rw [logb_self_eq_one]
      all_goals norm_num
    have h2 : logb 10 5 = 1 - logb 10 2 := by
      have h3 : logb 10 5 = logb 10 (10 / 2) := by norm_num
      rw [h3]
      rw [logb_div (by norm_num) (by norm_num)]
      have h13 : logb 10 10 = 1 := by
        rw [logb_self_eq_one]
        all_goals norm_num
      simp [h13]
      <;> ring_nf <;> linarith
    linarith [h1, h2]
  · -- Show any element in the set ≤ 2 - logb 10 2
    rintro z ⟨x, y, hx, hy, h_eq, hz⟩
    have h3 : logb 10 x + logb 10 y = logb 10 (x * y) := by
      rw [← logb_mul (by positivity) (by positivity)]
    have h4 : x * y ≤ 50 := by
      have h5 : y = 20 - 2 * x := by linarith
      rw [h5]
      nlinarith [sq_nonneg (x - 5)]
    have h6 : logb 10 (x * y) ≤ logb 10 50 := by
      apply Real.logb_le_logb_of_le
      all_goals
        nlinarith [mul_pos hx hy, h4]
    have h7 : logb 10 50 = 2 - logb 10 2 := by
      have h8 : logb 10 50 = logb 10 (5 * 10) := by norm_num
      rw [h8]
      have h9 : logb 10 (5 * 10) = logb 10 5 + logb 10 10 := by
        rw [logb_mul (by positivity) (by positivity)]
      rw [h9]
      have h11 : logb 10 5 = 1 - logb 10 2 := by
        have h12 : logb 10 5 = logb 10 (10 / 2) := by norm_num
        rw [h12]
        rw [logb_div (by norm_num) (by norm_num)]
        have h13 : logb 10 10 = 1 := by
          rw [logb_self_eq_one]
          all_goals norm_num
        simp [h13]
        all_goals linarith
      have h13 : logb 10 10 = 1 := by
        rw [logb_self_eq_one]
        all_goals norm_num
      simp [h11, h13]
      all_goals linarith
    linarith [hz, h3, h6, h7]