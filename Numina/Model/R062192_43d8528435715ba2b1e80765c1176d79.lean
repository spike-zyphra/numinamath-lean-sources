import Mathlib

theorem number_theory_287193 :
    {(x, y) : ℕ × ℕ | 20 * x ^ 2 + 17 * y = 2017} = {(10, 1), (7, 61)} := by 
  ext ⟨x, y⟩
  simp 
  constructor 
  · -- Forward direction: If (x,y) satisfies the equation, then it is in the set
    rintro H
    have h1 : x ≤ 10 := by 
      nlinarith
    interval_cases x <;> omega 
  · -- Backward direction: If (x,y) is in the set, it satisfies the equation
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · norm_num 
    · norm_num