import Mathlib

theorem algebra_13490 {x : ℝ} (hx : x ≥ 0) (h : Real.sqrt x = x - 72) :
    x = 81 := by
  have h1 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
  have h2 : x - 72 ≥ 0 := by linarith [h, h1]
  have h3 : Real.sqrt x = x - 72 := h
  have h4 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have h5 : (x - 72) ^ 2 = x ^ 2 - 144 * x + 5184 := by ring
  have h6 : (Real.sqrt x) ^ 2 = (x - 72) ^ 2 := by
    rw [h3]
  rw [h4] at h6
  have h7 : x ^ 2 - 145 * x + 5184 = 0 := by
    nlinarith [h6, h5]
  have h8 : (x - 81) * (x - 64) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h8) with h9 h10
  ·
    linarith
  ·
    linarith -- contradict with h2: x >=72, but getting x=64 <72