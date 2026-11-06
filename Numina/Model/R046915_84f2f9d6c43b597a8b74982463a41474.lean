import Mathlib

theorem algebra_608668 :
    IsGreatest {w | ∃ x y z : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x + y + z = 1 ∧ w = x + y ^ 2 + z ^ 3} 1 := by
  constructor
  · -- Show that 1 is in the set, using x = 0, y = 0, z = 1 
    use 0, 0, 1 
    norm_num 
  · -- Now prove it's greatest
    intro w hw 
    rcases hw with ⟨x, y, z, hx₀, hy₀, hz₀, h₁, h₂⟩
    have h3 : x + y + z = 1 := h₁ 
    have h4 : x ≤ 1 := by nlinarith 
    have h5 : y ≤ 1 := by nlinarith 
    have h6 : z ≤ 1 := by nlinarith 
    nlinarith [sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x - y), 
      sq_nonneg (y - 0), sq_nonneg (z - 0), sq_nonneg (x - 0), 
      sq_nonneg (x + y - z), 
      mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ 1 - x by nlinarith), 
      mul_nonneg (show 0 ≤ y by nlinarith) (show 0 ≤ 1 - y by nlinarith), 
      mul_nonneg (show 0 ≤ z by nlinarith) (show 0 ≤ 1 - z by nlinarith)
    ]