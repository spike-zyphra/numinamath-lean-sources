import Mathlib

theorem algebra_235029 (V P : ℝ) (hV : V > 0) (hP : P > 0)
    (hP1 : P * 1.1 = V * 1.2) (hP2 : P * 1.1 * (1 + 9.5 / 100) = V * (1 + 9.5 / 100)) :
    V > P := by 
  have h1 : (1 + 9.5 / 100 : ℝ) > 0 := by norm_num
  have h2 : P * 1.1 * (1 + 9.5 / 100) = V * (1 + 9.5 / 100) := by 
    linarith [hP2]
  have h3 : P * 1.1 = V := by
    apply (mul_left_inj' (ne_of_gt h1)).mp 
    linarith 
  nlinarith