import Mathlib

theorem algebra_173044 (a m n p : ℝ) (ha : a < -3) (hm : m = (a + 2) / (a + 3)) (hn : n = (a + 1) / (a + 2)) (hp : p = a / (a + 1)) :
    max (max m n) p = m := by
  have h1 : m > n := by 
    rw [hm, hn]
    have h1 : a + 3 < 0 := by linarith
    have h2 : a + 2 < 0 := by linarith
    have pos3 : (a + 2) ^ 2 - (a + 1) * (a + 3) = 1 := by 
      linarith 
    have pos4 : (a + 3) * (a + 2) > 0 := mul_pos_of_neg_of_neg h1 h2 
    have h3 : (a + 2) / (a + 3) - (a + 1) / (a + 2) > 0 := by 
      have : (a + 2) / (a + 3) - (a + 1) / (a + 2) = 1 / ((a + 3) * (a + 2)) := by 
        field_simp [(show a + 3 ≠ 0 by linarith), (show a + 2 ≠ 0 by linarith)]
        nlinarith [pos3]
      rw [this]
      positivity 
    linarith 
  have h2 : m > p := by 
    rw [hm, hp]
    have h1 : a + 3 < 0 := by linarith 
    have h2 : a + 1 < 0 := by linarith 
    have pos3 : (a + 2) * (a + 1) - a * (a + 3) = 2 := by 
      linarith 
    have pos4 : (a + 3) * (a + 1) > 0 := mul_pos_of_neg_of_neg h1 h2 
    have h3 : (a + 2) / (a + 3) - a / (a + 1) > 0 := by 
      have : (a + 2) / (a + 3) - a / (a + 1) = 2 / ((a + 3) * (a + 1)) := by 
        field_simp [(show a + 3 ≠ 0 by linarith), (show a + 1 ≠ 0 by linarith)]
        nlinarith [pos3]
      rw [this]
      positivity 
    linarith 
  have h3 : max m n = m := by
    apply max_eq_left 
    linarith [h1] 
  have h4 : max (max m n) p = max m p := by 
    rw [h3] 
  have h5 : max m p = m := by 
    apply max_eq_left 
    linarith [h2] 
  rw [h4, h5]