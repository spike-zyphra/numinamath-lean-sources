import Mathlib

/-
Tyler has an infinite geometric series with sum 10 . He increases the first term of his sequence by 4 and swiftly changes the subsequent terms so that the common ratio remains the same, creating a new geometric series with sum 15. Compute the common ratio of Tyler's series.
-/

theorem algebra_610682 {a r : ℝ } (hr : abs r < 1) (h1 : 10 = a / (1 - r)) (h2 : 15 = (a + 4) / (1 - r)): r = 1/5  := by
  -- just a simple calculation based on the definition of geometric series sum.
  have ne0: 1-r ≠ 0 := by 
    by_contra h; 
    have : r = 1 := by linarith
    rw [this] at hr; norm_num at hr

  have l1 : (a + 4) / (1 - r) - a / (1 - r) = 15 - 10 := by linarith
  have l2 : (a + 4) / (1 - r) - a / (1 - r) = 4 / (1-r) := by ring_nf
  rw [l2] at l1
  have : (15:ℝ) - 10 = 5 := by norm_num
  rw [this] at l1
  have : 4 = 5 * (1-r) := by exact (mul_inv_eq_iff_eq_mul₀ ne0).mp l1
  ring_nf at this; 
  have : r * 5 = 5-4 := by linarith
  have : r * 5 = 1 := by linarith
  field_simp; linarith
