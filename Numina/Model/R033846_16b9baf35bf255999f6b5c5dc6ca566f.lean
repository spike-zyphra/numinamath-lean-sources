import Mathlib

theorem algebra_13790 :
  IsGreatest {k | ∃ x y : ℝ, x ^ 2 - y ^ 2 = 1 / 22 ∧ x ≠ 0 ∧ k = (1 - 22 * x * y) / x ^ 2} (55 / 2) := by
  constructor
  · -- Show that 55 / 2 is in the set.
    use Real.sqrt (2 / 33)
    use - (Real.sqrt (2 / 33) / 2)
    constructor
    · -- Show that x^2 - y^2 = 1/22.
      have h1 : (Real.sqrt (2 / 33) : ℝ) ^ 2 = 2 / 33 := Real.sq_sqrt (by norm_num)
      have h2 : ( - (Real.sqrt (2 / 33) / 2) ) ^ 2 = (Real.sqrt (2 / 33) / 2) ^ 2 := by ring
      have h3 : (Real.sqrt (2 / 33) / 2) ^ 2 = (2 / 33) / 4 := by
        calc
          (Real.sqrt (2 / 33) / 2) ^ 2 = (Real.sqrt (2 / 33) ^ 2) / 4 := by ring
          _ = (2 / 33) / 4 := by rw [h1]
      have h4 : (Real.sqrt (2 / 33) : ℝ) ^ 2 - (- (Real.sqrt (2 / 33) / 2) ) ^ 2 = 1 / 22 := by
        rw [h2, h3]
        linarith [h1]
      linarith [h4]
    constructor
    · -- Show that x ≠ 0
      have h5 : Real.sqrt (2 / 33 : ℝ) > 0 := by
        apply Real.sqrt_pos.mpr
        all_goals norm_num
      have hne : Real.sqrt (2 / 33 : ℝ) ≠ 0 := by
        linarith [h5]
      exact hne
    · -- Show that 55 / 2 = (1 - 22 * x * y) / x ^ 2
      have h1 : (Real.sqrt (2 / 33) : ℝ) ^ 2 = 2 / 33 := Real.sq_sqrt (by norm_num)
      have eq1 : (1 - 22 * (Real.sqrt (2 / 33) ) * (- (Real.sqrt (2 / 33) / 2) ) ) / (Real.sqrt (2 / 33) ) ^ 2 = 55 / 2 := by
        have h2 : (Real.sqrt (2 / 33) : ℝ) ^ 2 = 2 / 33 := h1
        have h8 : 1 - 22 * (Real.sqrt (2 / 33) ) * (- (Real.sqrt (2 / 33) / 2) ) = 5 / 3 := by
          nlinarith [Real.sqrt_nonneg (2 / 33), h1, sq_nonneg (Real.sqrt (2 / 33) ^ 2)]
        rw [h8, h1]
        norm_num
      linarith [eq1]
  · -- Show that 55 / 2 is greatest
    intro k hk
    rcases hk with ⟨x, y, h1, hxne, hk⟩
    have h2 : (1 - 22 * x * y) / x ^ 2 ≤ 55 / 2 := by
      have hne : x ^ 2 > 0 := by
        exact sq_pos_of_ne_zero hxne
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x ^ 2 - 2 / 33), sq_nonneg (y ^ 2 - 1 / 66), sq_nonneg (x * y +1 / 33), sq_nonneg (x - (y * (-2))), sq_nonneg (x + 2 * y), sq_nonneg (x * 2 + y), sq_nonneg (x ^ 2 - 2 / 33), sq_nonneg (x * 33), sq_nonneg (y * 33)]
    linarith [hk, h2]