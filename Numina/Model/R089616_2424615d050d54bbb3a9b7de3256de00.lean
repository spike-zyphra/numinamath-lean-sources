import Mathlib

theorem algebra_159326 (a : ℝ) (ha : a < -3) (m n p : ℝ)
    (hm : m = (a + 2) / (a + 3)) (hn : n = (a + 1) / (a + 2))
    (hp : p = a / (a + 1)) :
    max (max m n) p = m := by
  rw [hm, hn, hp]
  have h1 : (a + 2) / (a + 3) > (a + 1) / (a + 2) := by
    have h2 : (a + 3) < 0 := by linarith 
    have h3 : (a + 2) < 0 := by linarith
    have h4 : (a + 1) < 0 := by linarith
    have h5 : (a + 2) / (a + 3) - (a + 1) / (a + 2) > 0 := by
      have h6 : (a + 2) / (a + 3) - (a + 1) / (a + 2) = ((a + 2) ^ 2 - (a + 1) * (a + 3)) / ((a + 3) * (a + 2)) := by
        field_simp [(show a + 3 ≠ 0 by linarith), (show a + 2 ≠ 0 by linarith)]
        <;> ring
      rw [h6]
      have h7 : ((a + 2) ^ 2 - (a + 1) * (a + 3)) > 0 := by nlinarith
      have h8 : (a + 3) * (a + 2) > 0 := by
        have h9 : (a + 3) < 0 := by linarith 
        have h10 : (a + 2) < 0 := by linarith
        have h11 : (a + 3) * (a + 2) > 0 := mul_pos_of_neg_of_neg (by linarith) (by linarith)
        exact h11
      apply div_pos
      linarith
      all_goals linarith 
    linarith 
  have h2 : (a + 2) / (a + 3) > a / (a + 1) := by
    have h2 : (a + 3) < 0 := by linarith
    have h3 : (a + 2) < 0 := by linarith
    have h4 : (a + 1) < 0 := by linarith
    have h5 : (a + 2) / (a + 3) - a / (a + 1) > 0 := by
      have h6 : (a + 2) / (a + 3) - a / (a + 1) = ((a + 2) * (a + 1) - a * (a + 3)) / ((a + 3) * (a + 1)) := by
        field_simp [(show a + 3 ≠ 0 by linarith), (show a + 1 ≠ 0 by linarith)]
        <;> ring 
      rw [h6]
      have h7 : ((a + 2) * (a + 1) - a * (a + 3)) > 0 := by nlinarith
      have h8 : (a + 3) * (a + 1) > 0 := by 
        have h9 : (a + 3) < 0 := by linarith
        have h10 : (a + 1) < 0 := by linarith
        have h11 : (a + 3) * (a + 1) > 0 := mul_pos_of_neg_of_neg (by linarith) (by linarith)
        exact h11
      apply div_pos
      linarith
      all_goals linarith
    linarith 
  have hmn : max ((a + 2) / (a + 3)) ((a + 1) / (a + 2)) = (a + 2) / (a + 3) := by
    apply max_eq_left 
    linarith [h1] 
  have hmax : max (max ((a + 2) / (a + 3)) ((a + 1) / (a + 2))) (a / (a + 1)) = (a + 2) / (a + 3) := by
    rw [hmn]
    apply max_eq_left 
    linarith [h2] 
  exact hmax