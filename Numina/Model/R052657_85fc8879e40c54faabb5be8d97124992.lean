import Mathlib

theorem algebra_9568 {x y : ℝ} (A B : ℝ × ℝ)
    (hA : A = (x, 16)) (hB : B = (24, -16))
    (hM : (-36, y) = ((A.1 + B.1) / 2, (A.2 + B.2) / 2)) :
    y - x = 96 := by
  rw [hA, hB] at hM
  simp at hM 
  have eq1 : (x + 24) / 2 = -36 := by 
    linarith 
  have eq2 : y = 0 := by 
    linarith 
  have hx : x = -96 := by 
    linarith 
  rw [eq2, hx]
  norm_num