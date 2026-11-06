import Mathlib

  theorem algebra_289979 :
    {(x, y) : ℝ × ℝ | 37*x+92*y=5043 ∧ 92*x+37*y=2568} = {(7, 52)} := by 
  ext ⟨x, y⟩
  simp
  constructor
  · -- Forward
    rintro ⟨h1, h2⟩
    have eq1 : x = 7 := by
      linarith
    have eq2 : y = 52 := by 
      linarith
    exact ⟨eq1, eq2⟩
  · -- Backward
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    · norm_num