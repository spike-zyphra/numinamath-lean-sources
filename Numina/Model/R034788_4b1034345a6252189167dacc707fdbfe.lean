import Mathlib

theorem algebra_240496 {x y : ℝ} (hx : x > 2 * y) (hy : y > 0) (h : 2 * Real.log (x - 2 * y) = Real.log x + Real.log y) :
    x / y = 4 := by
  have h1 : x - 2 * y > 0 := by linarith
  have h2 : x > 0 := by nlinarith
  have h3 : 2 * Real.log (x - 2 * y) = Real.log ((x - 2 * y) ^ 2) := by
    simp [Real.log_pow]
    <;> ring_nf <;> simp [Real.log_pow]

  have h4 : Real.log x + Real.log y = Real.log (x * y) := by
    rw [Real.log_mul (by positivity) (by positivity)]

  rw [h3, h4] at h

  have h5 : (x - 2 * y) ^ 2 = x * y := by
    have h6 : Real.log ((x - 2 * y) ^ 2) = Real.log (x * y) := h
    have h7 : (x - 2 * y) ^ 2 > 0 := by positivity
    have h8 : x * y > 0 := by positivity
    have h9 : (x - 2 * y) ^ 2 = x * y := by
      apply Real.log_injOn_pos (Set.mem_Ioi.mpr h7) (Set.mem_Ioi.mpr h8) h6
    linarith

  have h6 : (x - 2 * y) ^ 2 - x * y = 0 := by linarith
  have h7 : x ^ 2 - 5 * x * y + 4 * y ^ 2 = 0 := by
    nlinarith
  have h8 : (x - y) * (x - 4 * y) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- Case x - y = 0, so x = y, which leads to a contradiction with x > 2y
    have h10 : x = y := by linarith
    nlinarith [h10, hy]
  · -- Case x - 4y = 0, so x = 4y, which leads to x / y = 4
    have h11 : x = 4 * y := by linarith
    have h12 : x / y = 4 := by
      have h13 : y > 0 := hy
      have h14 : x = 4 * y := h11
      field_simp [h13]
      <;> nlinarith
    exact h12