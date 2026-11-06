import Mathlib

theorem inequalities_103598 {x y : ℝ} (h₀ : x^7 > y^6) (h₁ : y^7 > x^6) : x + y > 2 := by
  have hx : x > 0 := by
    by_contra h
    push_neg at h
    have h4 : y ^ 7 > 0 := by nlinarith [h₁, show x ^ 6 ≥ 0 by positivity]
    have hy : y > 0 := by
      by_contra h
      push_neg at h
      have h8 : y ≤ 0 := by linarith
      have h9 : y ^ 7 ≤ 0 := by
        have h10 : y ≤ 0 := h8
        have h11 : y ^ 6 ≥ 0 := by positivity
        have h12 : y ^ 7 = y * (y ^ 6) := by ring
        nlinarith
      linarith
    have h14 : x ^ 7 > 0 := by
      nlinarith [h₀, show y ^ 6 > 0 by positivity]
    -- Now we prove x > 0 from x^7 > 0
    by_contra h
    push_neg at h
    have h7 : x ^ 7 ≤ 0 := by
      have h8 : x ≤ 0 := by linarith
      have h77 : x ^ 7 ≤ 0 := by
        have h88 : x ≤ 0 := h8
        have h11 : x ^ 6 ≥ 0 := by positivity
        have h12 : x ^ 7 = x * (x ^ 6) := by ring
        nlinarith
      linarith
    linarith
  have hy : y > 0 := by
    by_contra h
    push_neg at h
    have h4 : y ^ 7 ≤ 0 := by
      have h8 : y ≤ 0 := by linarith
      have h77 : y ^ 7 ≤ 0 := by
        have h88 : y ≤ 0 := h8
        have h11 : y ^ 6 ≥ 0 := by positivity
        have h12 : y ^ 7 = y * (y ^ 6) := by ring
        nlinarith
      linarith
    -- Now contradiction with h₁
    nlinarith [show x ^ 6 > 0 by positivity, h₁, h4]
  have h16 : x * y > 1 := by
    have h18 : x ^ 7 * y ^ 7 > y ^ 6 * x ^ 6 := by
      nlinarith [h₀, h₁, show x ^ 6 > 0 by positivity, show y ^ 6 > 0 by positivity, mul_pos (show 0 < x by linarith) (show 0 < y by linarith)]
    have h19 : x ^ 7 * y ^ 7 = (x * y) ^ 7 := by ring
    have h20 : y ^ 6 * x ^ 6 = (x * y) ^ 6 := by ring
    rw [h19, h20] at h18
    have h21 : (x * y) ^ 7 > (x * y) ^ 6 := h18
    have h22 : (x * y) ^ 6 > 0 := by positivity
    have h23 : (x * y) ^ 7 - (x * y) ^ 6 > 0 := by linarith
    have h24 : (x * y) ^ 6 * ((x * y) - 1) > 0 := by
      nlinarith
    have h25 : (x * y) - 1 > 0 := by
      nlinarith [show (x * y) ^ 6 > 0 by positivity]
    nlinarith
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x * y - 1), mul_pos hx hy, h16]