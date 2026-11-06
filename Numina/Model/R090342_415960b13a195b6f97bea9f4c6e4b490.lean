import Mathlib

theorem algebra_146595 (x : ℝ) (hx : x > 0) (hne4 : x ≠ 4) (hne9 : x ≠ 9) :
    ((2 + Real.sqrt x) ^ (-1 : ℤ) + 1) ^ (-1 : ℤ) = (x - Real.sqrt x - 6) / (x - 9) := by
  have h1 : Real.sqrt x > 0 := by positivity
  have h2 : (2 + Real.sqrt x) ^ (-1 : ℤ) = 1 / (2 + Real.sqrt x) := by
    simp [zpow_neg_one]
  have h3 : (2 + Real.sqrt x) ^ (-1 : ℤ) + 1 = (3 + Real.sqrt x) / (2 + Real.sqrt x) := by
    rw [h2]
    field_simp
    <;> ring
  have h4 : ((2 + Real.sqrt x) ^ (-1 : ℤ) + 1) ^ (-1 : ℤ) = (2 + Real.sqrt x) / (3 + Real.sqrt x) := by
    rw [h3]
    field_simp
    <;> ring
  have h5 : (2 + Real.sqrt x) / (3 + Real.sqrt x) = (x - Real.sqrt x - 6) / (x - 9) := by
    have h51 : (3 + Real.sqrt x) ≠ 0 := by
      by_contra h'
      have h6 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
      have h7 : Real.sqrt x = -3 := by nlinarith
      linarith [Real.sqrt_nonneg x]
    have h52 : (x - 9) ≠ 0 := by
      intro h'
      apply hne9
      linarith
    field_simp
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith [hx]), Real.sqrt_nonneg x]
  rw [h4, h5]
  all_goals norm_num
  all_goals ring_nf
  all_goals nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith [hx])]