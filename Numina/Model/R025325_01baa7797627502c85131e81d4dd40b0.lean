import Mathlib

theorem algebra_196329 {x y : ℝ} : (x - 10)^2 + (y - 11)^2 + (x - y)^2 = 1 / 3 ↔
    x = 10 + 1 / 3 ∧ y = 10 + 2 / 3 := by
  constructor
  · -- Assume (x - 10)^2 + (y - 11)^2 + (x - y)^2 = 1 / 3, prove x = 10 + 1 / 3 ∧ y = 10 + 2 / 3
    intro h
    have eq1 : (x - 10 : ℝ) ^ 2 + (y - 11 : ℝ) ^ 2 + (x - y : ℝ) ^ 2 = 1 / 3 := by linarith
    have eq2 : (x - (10 + 1 / 3)) ^ 2 + (y - (10 + 2 / 3)) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (x - (10 + 1 / 3)), sq_nonneg (y - (10 + 2 / 3)), 
          sq_nonneg (x - y + 1 / 3), sq_nonneg ((x - 10) - (y - 11)), 
          sq_nonneg ((x - y) + 1 / 3)]
    have h3 : x - (10 + 1 / 3) = 0 := by 
      nlinarith [sq_nonneg (x - (10 + 1 / 3)), sq_nonneg (y - (10 + 2 / 3)), 
          eq2]
    have h4 : y - (10 + 2 / 3) = 0 := by 
      nlinarith [sq_nonneg (x - (10 + 1 / 3)), sq_nonneg (y - (10 + 2 / 3)), 
          eq2]
    constructor
    · linarith [h3]
    · linarith [h4]
  · -- Assume x = 10 + 1 / 3 ∧ y = 10 + 2 / 3, prove (x - 10)^2 + (y - 11)^2 + (x - y)^2 = 1 / 3
    rintro ⟨hx, hy⟩
    have h1 : x = 10 + 1 / 3 := hx
    have h2 : y = 10 + 2 / 3 := hy
    rw [h1, h2]
    norm_num