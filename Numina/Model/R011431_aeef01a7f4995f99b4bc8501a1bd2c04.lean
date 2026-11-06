import Mathlib

theorem algebra_391 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : 1 / a + 1 / b - 1 / d = 1 / 6)
    (h2 : 1 / a + 1 / c - 1 / d = 1 / 5)
    (h3 : 1 / b + 1 / c - 1 / d = 1 / 4)
    (h4 : 1 / a + 1 / b + 1 / c - 1 / d = 1 / 3) :
    1 / (1 / a + 1 / b + 1 / c) = 60 / 23 := by
  have eq1 : 1 / a + 1 / b + 1 / c = 23 / 60 := by
    have eq2 : 1 / d = 1 / 20 := by
      have eq5 : (1 / a + 1 / b - 1 / d) + (1 / a + 1 / c - 1 / d) + (1 / b + 1 / c - 1 / d) = 1 / 6 + 1 / 5 + 1 / 4 := by
        linarith [h1, h2, h3]
      have eq6 : (1 / a + 1 / b - 1 / d) + (1 / a + 1 / c - 1 / d) + (1 / b + 1 / c - 1 / d) = 2 * (1 / a + 1 / b + 1 / c) - 3 * (1 / d) := by 
        ring
      have eq7 : 1 / a + 1 / b + 1 / c = 1 / 3 + 1 / d := by 
        linarith [h4]
      rw [eq6] at eq5 
      rw [eq7] at eq5 
      norm_num at eq5 ⊢
      linarith
    have eq9 : 1 / a + 1 / b + 1 / c = 23 / 60 := by 
      have eq7 : 1 / a + 1 / b + 1 / c = 1 / 3 + 1 / d := by 
        linarith [h4]
      rw [eq7]
      rw [eq2]
      norm_num 
    exact_mod_cast eq9 
  have h5 : 1 / (1 / a + 1 / b + 1 / c) = 60 / 23 := by
    rw [eq1]
    all_goals norm_num 
  exact_mod_cast h5