import Mathlib

theorem algebra_233474 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a + b + c + d = 100) (h2 : a / (b + c + d) + b / (a + c + d) + c / (a + b + d) +
    d / (a + b + c) = 95) :
    1 / (b + c + d) + 1 / (a + c + d) + 1 / (a + b + d) + 1 / (a + b + c) = 99 / 100 := by

  have h3 : b + c + d = 100 - a := by 
    linarith
  
  have h4 : a + c + d = 100 - b := by 
    linarith
  
  have h5 : a + b + d = 100 - c := by 
    linarith

  have h6 : a + b + c = 100 - d := by 
    linarith
  
  have eq1 : a / (b + c + d) + b / (a + c + d) + c / (a + b + d) + d / (a + b + c) =
      a / (100 - a) + b / (100 - b) + c / (100 - c) + d / (100 - d) := by 
    rw [h3, h4, h5, h6]

  rw [eq1] at h2
  
  have eq2 : 1 / (b + c + d) + 1 / (a + c + d) + 1 / (a + b + d) + 1 / (a + b + c) =
      1 / (100 - a) + 1 / (100 - b) + 1 / (100 - c) + 1 / (100 - d) := by 
    rw [h3, h4, h5, h6]

  rw [eq2]

  have eq3 : a / (100 - a) + b / (100 - b) + c / (100 - c) + d / (100 - d) =
      100 * (1 / (100 - a) + 1 / (100 - b) + 1 / (100 - c) + 1 / (100 - d)) - 4 := by 
    field_simp [(show 100 - a ≠ 0 by nlinarith), (show 100 - b ≠ 0 by nlinarith), 
        (show 100 - c ≠ 0 by nlinarith), (show 100 - d ≠ 0 by nlinarith)]
    ring

  have eq4 : 100 * (1 / (100 - a) + 1 / (100 - b) + 1 / (100 - c) + 1 / (100 - d)) - 4 = 95 := by 
    linarith [h2, eq3]

  have eq5 : 1 / (100 - a) + 1 / (100 - b) + 1 / (100 - c) + 1 / (100 - d) = 99 / 100 := by
    linarith

  linarith [eq5]