import Mathlib

theorem algebra_2178 {a m n p : ℝ} (ha : a < -3) (hm : m = (a + 2) / (a + 3)) (hn : n = (a + 1) / (a + 2)) (hp : p = a / (a + 1)) : p < n ∧ n < m := by

  have h1 : p < n := by 
    rw [hp, hn]
    have h2 : a < -3 := ha
    have h3 : a + 1 < 0 := by linarith
    have h4 : a + 2 < 0 := by linarith
    have h5 : (a / (a + 1) - (a + 1) / (a + 2)) < 0 := by
      have pos1 : (a + 1) * (a + 2) > 0 := by
        have h11 : a + 1 < 0 := by linarith
        have h12 : a + 2 < 0 := by linarith
        nlinarith
      have h6 : a / (a + 1) - (a + 1) / (a + 2) = (-1) / ((a + 1) * (a + 2)) := by 
        field_simp [(show (a + 1 : ℝ) ≠ 0 by nlinarith), (show (a + 2 : ℝ) ≠ 0 by nlinarith)]
        ring
      rw [h6]
      have : (-1 : ℝ) / ((a + 1) * (a + 2)) < 0 := by
        apply div_neg_of_neg_of_pos
        norm_num
        all_goals nlinarith
      linarith
    linarith
  have h2 : n < m := by 
    rw [hn, hm]
    have h3 : a < -3 := ha
    have h4 : a + 2 < 0 := by linarith
    have h5 : a + 3 < 0 := by linarith
    have h6 : ((a + 1) / (a + 2) - (a + 2) / (a + 3)) < 0 := by
      have pos1 : (a + 2) * (a + 3) > 0 := by
        have h11 : a + 2 < 0 := by linarith
        have h12 : a + 3 < 0 := by linarith
        nlinarith
      have h7 : ( (a + 1) / (a + 2) - (a + 2) / (a + 3) ) = (-1) / ((a + 2) * (a + 3)) := by 
        field_simp [(show (a + 2 : ℝ) ≠ 0 by nlinarith), (show (a + 3 : ℝ) ≠ 0 by nlinarith)]
        ring
      rw [h7]
      have : (-1 : ℝ) / ((a + 2) * (a + 3)) < 0 := by
        apply div_neg_of_neg_of_pos
        norm_num
        all_goals nlinarith
      linarith
    linarith
  constructor
  · exact h1
  · exact h2