import Mathlib

open Real Set

theorem algebra_6117 : IsGreatest {y : ℝ | ∃ x, y = 36 / sqrt (x ^ 2 + 8 * x + 97)} 4 := by
  constructor
  · -- First, we prove that 4 belongs to the set, i.e., there exists some x where the value is 4
    use -4
    have h1 : sqrt ((-4 : ℝ) ^ 2 + 8 * (-4 : ℝ) + 97) = 9 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
    norm_num
  · -- Now, we need to show that 4 is the greatest element in the set
    rintro y hy
    rcases hy with ⟨x, hx⟩
    have h2 : x ^ 2 + 8 * x + 97 ≥ 81 := by
      nlinarith [sq_nonneg (x + 4)]
    have h3 : sqrt (x ^ 2 + 8 * x + 97) ≥ 9 := by
      have h4 : sqrt (x ^ 2 + 8 * x + 97) ≥ sqrt (81 : ℝ) := Real.sqrt_le_sqrt (show x ^ 2 + 8 * x + 97 ≥ (81 : ℝ) by linarith)
      have h5 : sqrt (81 : ℝ) = 9 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith [h4, h5]
    have h6 : (36 : ℝ) / sqrt (x ^ 2 + 8 * x + 97) ≤ 4 := by
      have h7 : sqrt (x ^ 2 + 8 * x + 97) ≥ 9 := by
        have h4 : sqrt (x ^ 2 + 8 * x + 97) ≥ sqrt (81 : ℝ) := Real.sqrt_le_sqrt (show x ^ 2 + 8 * x + 97 ≥ (81 : ℝ) by linarith)
        have h5 : sqrt (81 : ℝ) = 9 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        linarith [h4, h5]
      have h8 : sqrt (x ^ 2 + 8 * x + 97) > 0 := by
        apply Real.sqrt_pos.mpr
        nlinarith [sq_nonneg (x + 4)]
      apply (div_le_iff (by positivity)).mpr
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 8 * x + 97), h3]
    linarith [hx, h6]