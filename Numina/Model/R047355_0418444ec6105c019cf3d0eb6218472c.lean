import Mathlib

theorem algebra_310982 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a + 2 * b = 1) (h2 : c + 2 * d = 1) :
    1 / a + 1 / (b * c * d) ≥ 25 := by
  have h3 : a = 1 - 2 * b := by linarith
  have h4 : c = 1 - 2 * d := by linarith
  have hb1 : 1 - 2 * b > 0 := by
    rw [show 1 - 2 * b = a by linarith]
    linarith
  have h5 : 1 - 2 * d > 0 := by
    rw [show 1 - 2 * d = c by linarith]
    linarith
  have h7 : 1 / a + 1 / (b * c * d) = 1 / (1 - 2 * b) + 1 / (b * (1 - 2 * d) * d) := by
    rw [show a = 1 - 2 * b by linarith, show c = 1 - 2 * d by linarith]
  rw [h7]
  have h8 : 1 / (1 - 2 * b) + 1 / (b * (1 - 2 * d) * d) ≥ 25 := by
    have h9 : 0 < (1 - 2 * b) * (b * (1 - 2 * d) * d) := by
      positivity
    have h10 : 1 / (1 - 2 * b) + 1 / (b * (1 - 2 * d) * d) - 25 ≥ 0 := by
      have h11 : 1 / (1 - 2 * b) + 1 / (b * (1 - 2 * d) * d) - 25 =
          ( (b * (1 - 2 * d) * d) + (1 - 2 * b) - 25 * ( (1 - 2 * b) * (b * (1 - 2 * d) * d) ) ) / ( (1 - 2 * b) * (b * (1 - 2 * d) * d) ) := by
        field_simp
        all_goals
          ring
      rw [h11]
      have h12 : ( (b * (1 - 2 * d) * d) + (1 - 2 * b) - 25 * ( (1 - 2 * b) * (b * (1 - 2 * d) * d) ) ) ≥ 0 := by
        nlinarith [sq_nonneg (b - 2 / 5), sq_nonneg (d - 1 / 4), sq_nonneg (b * (d - 1 / 4)), sq_nonneg ((1 - 2 * d) * (b - 2 / 5)), sq_nonneg ( (1 - 2 * b) - (1 / 5) ), sq_nonneg ( (1 - 2 * d) - (1 / 2) ), mul_pos hb (show 0 < 1 - 2 * b by linarith [hb1]), mul_pos hb (show 0 < 1 - 2 * d by linarith [h5]), mul_pos (show 0 < 1 - 2 * b by linarith [hb1]) (show 0 < 1 - 2 * d by linarith [h5]), mul_pos (show 0 < 1 - 2 * b by linarith [hb1]) (show 0 < d by linarith), sq_nonneg (b * d - 2 / 5 * 1 / 4), mul_pos hb hc, mul_pos hb (show 0 < 1 - 2 * b by linarith [hb1]), mul_pos hb (show 0 < 1 - 2 * d by linarith [h5]), mul_pos (show 0 < 1 - 2 * b by linarith [hb1]) (show 0 < 1 - 2 * d by linarith [h5]), mul_pos (show 0 < 1 - 2 * d by linarith [h5]) (show 0 < d by linarith) ]
      have h13 : ( (1 - 2 * b) * (b * (1 - 2 * d) * d) ) > 0 := by positivity
      have h14 : ( (b * (1 - 2 * d) * d) + (1 - 2 * b) - 25 * ( (1 - 2 * b) * (b * (1 - 2 * d) * d) ) ) / ( (1 - 2 * b) * (b * (1 - 2 * d) * d) ) ≥ 0 := by
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith
  linarith