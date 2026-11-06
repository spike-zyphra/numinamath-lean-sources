import Mathlib

open Matrix

theorem calculus_17275 : {(a, b) : ℝ×ℝ | ![2, a, -7] ×₃ ![5, 4, b] = 0} = {(8/5, -35/2)}  := by
  ext ⟨a, b⟩
  simp [crossProduct, Fin.sum_univ_three, mul_add, add_mul]
  constructor
  · -- Assume the cross product is zero, prove the ordered pair
    rintro ⟨h1, h2, h3⟩
    have hb : b = -35 / 2 := by 
      linarith

    have ha : a = 8 / 5 := by
      linarith

    simp [ha, hb]
  · -- Assume the ordered pair, prove the cross product is zero
    rintro ⟨rfl, rfl⟩
    
    constructor
    · -- First equation
      norm_num
    constructor
    · -- Second equation
      norm_num
    · -- Third equation
      norm_num