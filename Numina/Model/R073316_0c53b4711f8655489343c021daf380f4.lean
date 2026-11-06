import Mathlib

theorem algebra_145217 (x : ℝ) (hx : 6 * x ^ 2 - x - 2 ≠ 0) :
    (4 * x ^ 2 - 4 * x - 3) / (6 * x ^ 2 - x - 2) = (2 * x - 3) / (3 * x - 2) := by
  have h1 : 6 * x ^ 2 - x - 2 = (2 * x + 1) * (3 * x - 2) := by ring
  have h2 : 4 * x ^ 2 - 4 * x - 3 = (2 * x + 1) * (2 * x - 3) := by ring
  rw [h1, h2]
  have h3 : 2 * x + 1 ≠ 0 := by
    by_contra h
    have h4 : (2 * x + 1) * (3 * x - 2) = 0 := by
      rw [h]
      norm_num
    have h5 : (6 * x ^ 2 - x - 2) = 0 := by
      nlinarith
    contradiction
  have h4 : 3 * x - 2 ≠ 0 := by
    by_contra h
    have h5 : (2 * x + 1) * (3 * x - 2) = 0 := by
      rw [h]
      norm_num
    have h6 : (6 * x ^ 2 - x - 2) = 0 := by
      nlinarith
    contradiction
  field_simp [h3, h4, show (6 * x ^ 2 - x - 2) ≠ 0 by assumption]
  <;> ring_nf <;> field_simp <;> tauto