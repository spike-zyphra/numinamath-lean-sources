import Mathlib

theorem algebra_131228 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : 2 * x + y / 2 ≠ 0) :
    ((2 * x + y / 2) ^ (-1 : ℤ)) * ((2 * x) ^ (-1 : ℤ) + (y / 2) ^ (-1 : ℤ)) =
    (x * y) ^ (-1 : ℤ) := by
  have eq1 : (2 * x + y / 2) ^ (-1 : ℤ) = 1 / (2 * x + y / 2) := by
    simp [zpow_neg_one]
  have eq2 : (2 * x) ^ (-1 : ℤ) = 1 / (2 * x) := by
    simp [zpow_neg_one]
  have eq3 : (y / 2) ^ (-1 : ℤ) = 1 / (y / 2) := by
    simp [zpow_neg_one]
  have eq4 : (x * y) ^ (-1 : ℤ) = 1 / (x * y) := by
    simp [zpow_neg_one]
  rw [eq1, eq2, eq3, eq4]
  have eq5 : 1 / (y / 2) = 2 / y := by
    field_simp [hy]
    <;> ring
  have eq6 : 1 / (2 * x) + (2 / y) = (y + 4 * x) / (2 * x * y) := by
    field_simp [hx, hy]
    <;> ring
  have eq7 : 1 / (2 * x + y / 2) = 2 / (4 * x + y) := by
    have h1 : 2 * x + y / 2 = (4 * x + y) / 2 := by 
      linarith
    rw [h1]
    field_simp [(show (4 * x + y) ≠ 0 by 
      by_contra h1
      have h2 : 2 * x + y / 2 = 0 := by 
        have h3 : 2 * x + y / 2 = (4 * x + y) / 2 := by 
          linarith
        rw [h3]
        rw [h1]
        norm_num
      contradiction
    )]
  rw [eq5]
  rw [eq6]
  rw [eq7]
  have h1 : 4 * x + y ≠ 0 := by
    by_contra h1
    have h2 : 2 * x + y / 2 = 0 := by 
      have h3 : 2 * x + y / 2 = (4 * x + y) / 2 := by 
        linarith
      rw [h3]
      rw [h1]
      norm_num
    contradiction
  field_simp [hx, hy, h1]
  <;> ring