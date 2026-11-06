import Mathlib

theorem algebra_157159 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x > y)
    (z t : ℝ) (hz : z = (x + y) / 2) (ht : t = Real.sqrt (x * y)) (h : (x - y) = 3 * (z - t)) :
    x / y = 25 := by

  rw [hz, ht] at h
  have eq1 : 2 * (x - y) = 3 * ((x + y) - 2 * Real.sqrt (x * y)) := by
    nlinarith
  have eq2 : x + 5 * y = 6 * Real.sqrt (x * y) := by
    nlinarith [eq1, Real.sqrt_nonneg (x * y), Real.sqrt_nonneg (x * y)]
  have h3 : 0 ≤ x * y := by nlinarith
  have eq3 : (x + 5 * y) ^ 2 = 36 * (x * y) := by
    calc
      (x + 5 * y) ^ 2 = (6 * Real.sqrt (x * y)) ^ 2 := by
        rw [show 6 * Real.sqrt (x * y) = x + 5 * y by linarith [eq2]]
      _ = 36 * (Real.sqrt (x * y) ^ 2) := by
        ring_nf
      _ = 36 * (x * y) := by
        rw [Real.sq_sqrt (show (0 : ℝ) ≤ x * y by nlinarith)]

  have eq4 : x ^ 2 + 25 * y ^ 2 - 26 * (x * y) = 0 := by
    nlinarith [eq3, Real.sqrt_nonneg (x * y), Real.sqrt_nonneg (x * y)]

  have eq5 : (x - y) * (x - 25 * y) = 0 := by
    nlinarith [eq4, sq_pos_of_pos hx, sq_pos_of_pos hy]

  cases' (mul_eq_zero.1 eq5) with h6 h7
  · -- Case x - y = 0, which is a contradiction since x > y
    have h_eq : x = y := by
      linarith
    nlinarith
  · -- Case x - 25 * y = 0, which means x = 25 * y
    have h_eq : x = 25 * y := by
      linarith
    have h2 : x / y = 25 := by
      have h1 : y ≠ 0 := by nlinarith
      field_simp [h1]
      <;> nlinarith [h_eq, h_eq]
    exact h2