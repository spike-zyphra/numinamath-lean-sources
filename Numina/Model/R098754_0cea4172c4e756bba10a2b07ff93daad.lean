import Mathlib

theorem algebra_172723 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hle : a ≤ b ∧ b ≤ c) (hbound : c ≤ 2 * a) :
    b / a + c / b + a / c ≤ 7 / 2 := by
  rcases hle with ⟨h1, h2⟩
  have h3 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have h4 : b / a + c / b + a / c - 7 / 2 ≤ 0 := by
    have h5 : (b / a + c / b + a / c - 7 / 2) =
        ( (b ^ 2 * c + a ^ 2 * b + a * c ^ 2 - 7 / 2 * (a * b * c)) / (a * b * c) ) := by
      field_simp
      ring
    rw [h5]
    have hk : b ^ 2 * c + a ^ 2 * b + a * c ^ 2 - 7 / 2 * (a * b * c) ≤ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - 2 * a),
        sq_nonneg (c - a), sq_nonneg (b - a), sq_nonneg (c - b), 
        mul_nonneg (show 0 ≤ a by linarith [ha]) (show 0 ≤ b - a by linarith [h1]), 
        mul_nonneg (show 0 ≤ b by linarith [hb]) (show 0 ≤ c - b by linarith [h2]), 
        mul_nonneg (show 0 ≤ a by linarith [ha]) (show 0 ≤ c - a by linarith [show a ≤ c by linarith [h1, h2]]), 
        sq_nonneg (a * 2 - b), sq_nonneg (b * 2 - c), sq_nonneg (c * 2 - a * 2)]
    apply div_nonpos_of_nonpos_of_nonneg hk (by positivity)
  linarith [h4]