import Mathlib

theorem algebra_322104 {a : ℝ} (ha : a = Real.sqrt 5 - 2) : 3 * a^3 + 10 * a^2 - 12 * a + 6 = 6 - Real.sqrt 5 := by 
  have ha2 : a + 2 = Real.sqrt 5 := by 
    rw [ha]
    ring
  have h1 : (a + 2) ^ 2 = 5 := by 
    rw [ha2]
    rw [Real.sq_sqrt]
    all_goals norm_num
  have h2 : a ^ 2 + 4 * a - 1 = 0 := by 
    nlinarith 
  have h3 : a ^ 2 = 1 - 4 * a := by 
    linarith 
  have h4 : a ^ 3 = 17 * a - 4 := by 
    calc 
      a ^ 3 = a * a ^ 2 := by ring 
      _ = a * (1 - 4 * a) := by rw [h3]
      _ = a - 4 * a ^ 2 := by ring 
      _ = a - 4 * (1 - 4 * a) := by rw [h3]
      _ = 17 * a - 4 := by ring 
  have eq1 : 3 * a ^ 3 + 10 * a ^ 2 - 12 * a + 6 = 4 - a := by 
    rw [h4, h3]
    ring 
  rw [eq1]
  rw [ha]
  ring_nf
  <;> nlinarith [Real.sqrt_nonneg 5]