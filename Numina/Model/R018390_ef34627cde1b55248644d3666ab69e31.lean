import Mathlib

theorem algebra_155118 {x y z t : ℝ} (hy3 : x > y^3) (hy : y > z^3) (ht : z > t^3)
    (htx : t > x^3) : x * y * z * t > 0 := by
  by_cases h4 : x > 0
  · -- Assume x > 0.
    have h5 : t > 0 := by
      have h6 : x^3 > 0 := by
        positivity
      nlinarith
    have h8 : z > 0 := by
      have h9 : t > 0 := h5
      have h10 : t^3 > 0 := by
        positivity
      have h11 : z > t^3 := ht
      nlinarith
    have h10 : y > 0 := by
      have h11 : z > 0 := h8
      have h12 : z^3 > 0 := by
        positivity
      have h13 : y > z^3 := hy
      nlinarith
    have h14 : x > 0 := h4
    have h15 : y > 0 := h10
    have h16 : z > 0 := h8
    have h17 : t > 0 := h5
    positivity
  · -- Assume x ≤ 0.
    have h40 : x ≤ 0 := by linarith
    have h50 : y < 0 := by
      nlinarith [sq_nonneg (y), sq_nonneg (z), sq_nonneg (t), sq_nonneg (x), sq_nonneg (y^2), sq_nonneg (z^2), sq_nonneg (t^2), sq_nonneg (x^2)]
    have h60 : z < 0 := by
      nlinarith [sq_nonneg (y), sq_nonneg (z), sq_nonneg (t), sq_nonneg (x), sq_nonneg (y^2), sq_nonneg (z^2), sq_nonneg (t^2), sq_nonneg (x^2)]
    have h70 : t < 0 := by
      nlinarith [sq_nonneg (y), sq_nonneg (z), sq_nonneg (t), sq_nonneg (x), sq_nonneg (y^2), sq_nonneg (z^2), sq_nonneg (t^2), sq_nonneg (x^2)]
    have h100 : x * y > 0 := by
      have h140 : x < 0 := by
        nlinarith [sq_nonneg (x^2), sq_nonneg (y^2), sq_nonneg (z^2), sq_nonneg (t^2)]
      have h150 : y < 0 := by
        linarith
      have h160 : x * y > 0 := mul_pos_of_neg_of_neg h140 h150
      linarith
    have h101 : z * t > 0 := by
      have h141 : z < 0 := by
        linarith
      have h151 : t < 0 := by
        linarith
      have h161 : z * t > 0 := mul_pos_of_neg_of_neg h141 h151
      linarith
    have h102 : x * y * z * t > 0 := by
      have h1000 : x * y > 0 := h100
      have h1001 : z * t > 0 := h101
      have h1002 : (x * y) * (z * t) > 0 := mul_pos h1000 h1001
      ring_nf at h1002 ⊢
      linarith
    linarith