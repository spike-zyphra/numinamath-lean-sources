import Mathlib

theorem algebra_125 {a : ℝ} (ha : a = Real.sqrt 3 - 1) :
    a ^ 2015 + 2 * a ^ 2014 - 2 * a ^ 2013 = 0 := by

  have h_eq : a + 1 = Real.sqrt 3 := by 
    rw [ha]
    ring

  have h_sq : (a + 1) ^ 2 = 3 := by
    rw [h_eq]
    rw [Real.sq_sqrt]
    all_goals norm_num

  have h_quad : a^2 + 2 * a - 2 = 0 := by
    nlinarith [h_sq]

  have eq1 : a ^ 2015 + 2 * a ^ 2014 - 2 * a ^ 2013 = a ^ 2013 * (a^2 + 2*a - 2) := by 
    ring

  rw [eq1]
  rw [h_quad]
  all_goals norm_num