import Mathlib

theorem algebra_13414 {x : ℝ} (hx : x = 0 ∨ x > 0) (h : x = Real.sqrt x + 240) :
    x = 256 := by
  rcases hx with (rfl | hx)
  · -- Case x = 0, which leads to contradiction
    have h1 : Real.sqrt (0 : ℝ) = 0 := Real.sqrt_zero
    rw [h1] at h
    linarith
  · -- Case x > 0
    have h1 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
    have h2 : x - 240 = Real.sqrt x := by linarith
    have h4 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)
    have h5 : (x - 240) ^ 2 = x := by
      calc
        (x - 240) ^ 2 = (Real.sqrt x) ^ 2 := by rw [h2]
        _ = x := h4
    have h6 : x ^ 2 - 481 * x + 57600 = 0 := by
      nlinarith [h5]
    have h7 : (x - 256) * (x - 225) = 0 := by
      nlinarith [h6]
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- x - 256 = 0, so x = 256
      linarith
    · -- x - 225 = 0, so x = 225
      have h10 : x = 225 := by linarith
      have h11 : Real.sqrt x = 15 := by
        rw [h10]
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        <;> linarith
      rw [h11] at h2
      nlinarith [h10]