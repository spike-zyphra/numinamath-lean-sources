import Mathlib

theorem algebra_256146 {a c : ℝ} (ha : a ≠ 0) (hroots : {3, 1 / 3} = {x | a * x ^ 2 - 6 * x + c = 0}) :
    a + c = 18 / 5 := by 
  have h3 : 3 ∈ {x | a * x ^ 2 - 6 * x + c = 0} := by 
    rw [← hroots]
    simp
  have h1_3 : 1 / 3 ∈ {x | a * x ^ 2 - 6 * x + c = 0} := by 
    rw [← hroots]
    simp
  simp at h3 h1_3
  linarith