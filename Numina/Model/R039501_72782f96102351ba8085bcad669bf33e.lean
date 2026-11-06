import Mathlib

theorem algebra_606235 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    (1 + a * b * c) * (1 / a + 1 / b + 1 / c) ≥ 3 + a + b + c := by
  have h1 : 0 < a := by linarith
  have h2 : 0 < b := by linarith
  have h3 : 0 < c := by linarith
  have h4 : a * b * c > 0 := by positivity

  have h5 : (1 + a * b * c) * (1 / a + 1 / b + 1 / c) - (3 + a + b + c) ≥ 0 := by
    have h6 : (1 + a * b * c) * (1 / a + 1 / b + 1 / c) - (3 + a + b + c) =
        ( (1 + a * b * c) * (b * c + a * c + a * b) - (3 + a + b + c) * (a * b * c) ) / (a * b * c) := by
      field_simp
      <;> ring
    rw [h6]
    apply div_nonneg 
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        sq_nonneg (a * b * c - 1),
        mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb),
        mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hc),
        mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc),
        mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
        mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith),
        mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith)
      ]
    positivity
  linarith