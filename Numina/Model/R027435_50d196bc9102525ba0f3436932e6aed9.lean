import Mathlib

theorem algebra_3407 {p q r : ℝ} (hpqr : p > 0 ∧ q > 0 ∧ r > 0)
    (h1 : p^2 + p * q + q^2 = 211) (h2 : q^2 + q * r + r^2 = 259)
    (h3 : r^2 + r * p + p^2 = 307) : p * q + q * r + r * p = 253 := by
  rcases hpqr with ⟨hp, hq, hr⟩
  nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (r - p),
          mul_pos hp hq, mul_pos hp hr, mul_pos hq hr]