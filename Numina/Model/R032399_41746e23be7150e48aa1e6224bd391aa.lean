import Mathlib

theorem inequalities_137781 (a b c : ℝ) (ha : 0 < a) (hc : 0 < c) (hb : 0 < b)
    (h1 : a ≥ b ∧ b ≥ c) (h2 : a + b + c = 3) :
    a * b^2 + b * c^2 + c * a^2 ≤ 27 / 8 := by
  have h11 : a ≥ b := h1.1
  have h12 : b ≥ c := h1.2
  have h22 : a + b + c = 3 := h2
-- From the ordering, a is the largest. The terms square slopes faces a max.
  have h3 : a ≥ b := by linarith
  have h4 : b ≥ c := by linarith
  have h5 : a ≥ c := by linarith -- a >= b, b >=c implies a>=c

  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr h4), 
          mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr h5),
          mul_nonneg (sub_nonneg.mpr h4) (sub_nonneg.mpr h5),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]