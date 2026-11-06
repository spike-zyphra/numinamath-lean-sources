import Mathlib

theorem algebra_154501 :
    {(x, y) : ℝ × ℝ | (x - 2 * y) ^ 2 + (y - 1) ^ 2 = 0} = {(2, 1)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x - 2 * y) ^ 2 + (y - 1) ^ 2 = 0, prove (x = 2 ∧ y = 1)
    intro h
    have h1 : (x - 2 * y) ^ 2 ≥ 0 := by apply sq_nonneg
    have h2 : (y - 1) ^ 2 ≥ 0 := by apply sq_nonneg
    have h3 : (x - 2 * y) ^ 2 = 0 := by linarith
    have h4 : (y - 1) ^ 2 = 0 := by linarith
    have hy : y - 1 = 0 := by
      rwa [sq_eq_zero_iff] at h4
    have hy' : y = 1 := by linarith
    have h5 : x - 2 * y = 0 := by
      rw [sq_eq_zero_iff] at h3
      linarith
    rw [hy'] at h5
    have hx : x = 2 := by linarith
    exact ⟨hx, hy'⟩
  · -- Assume (x = 2 ∧ y = 1), prove (x - 2 * y) ^ 2 + (y - 1) ^ 2 = 0
    rintro ⟨hx, hy⟩
    rw [hx, hy]
    norm_num