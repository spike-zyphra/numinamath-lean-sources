import Mathlib

theorem algebra_93191 {k r : ℝ} (hk : 3 = k * 2 ^ r) (hr : 15 = k * 4 ^ r) :
    r = Real.logb 2 5 := by
  have eq5 : k = 3 / ((2 : ℝ) ^ r) := by
    have hne : (2 : ℝ) ^ r ≠ 0 := by positivity
    field_simp [hne]
    linarith [hk]

  have eq6 : (4 : ℝ) ^ r = ((2 : ℝ) ^ r) ^ 2 := by
    calc
      (4 : ℝ) ^ r = ( (2 : ℝ) ^ (2 : ℝ) ) ^ r := by norm_num
      _ = (2 : ℝ) ^ (2 * r : ℝ) := by rw [← Real.rpow_mul]; ring; all_goals linarith
      _ = ((2 : ℝ) ^ r) ^ 2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul]; ring; all_goals linarith

  rw [eq5] at hr
  rw [eq6] at hr

  have eq8 : (2 : ℝ) ^ r = 5 := by
    have hne : (2 : ℝ) ^ r ≠ 0 := by positivity
    have eq7 : 3 * ((2 : ℝ) ^ r) ^ 2 - 15 * ((2 : ℝ) ^ r) = 0 := by
      have eq8 : (3 / ((2 : ℝ) ^ r) ) * ((2 : ℝ) ^ r) ^ 2 = 3 * ((2 : ℝ) ^ r) := by
        field_simp [hne]
        <;> nlinarith
      nlinarith [sq_nonneg ((2 : ℝ) ^ r), eq8, hr]
    have eq9 : ((2 : ℝ) ^ r) * ((2 : ℝ) ^ r - 5) = 0 := by
      nlinarith [eq7]
    cases' (mul_eq_zero.1 eq9) with h10 h11
    · -- ((2 : ℝ) ^ r) = 0
      exfalso
      have h2 : (2 : ℝ) ^ r > 0 := by positivity
      nlinarith
    · -- ((2 : ℝ) ^ r - 5) = 0
      linarith [h11]

  -- From 2 ^ r = 5, solving for r gives r = logb 2 5.
  have eq20 : r = Real.logb (2 : ℝ) (5 : ℝ) := by
    rw [← eq8]
    field_simp [Real.logb_rpow]
    all_goals nlinarith

  linarith [eq20]