import Mathlib
open Real

theorem algebra_8088 (m : ℝ) (h : ∀ x, x^2 - 4 * x + m ≠ 0) :
    m - 4 > 0 ∧ m - 3 > 0 := by
  have h1 : m > 4 := by
    by_contra h2
    push_neg at h2
    have h3 : ∃ x : ℝ, x^2 - 4 * x + m = 0 := by
      use 2 + Real.sqrt (4 - m)
      have h4 : (Real.sqrt (4 - m)) ^ 2 = 4 - m := by 
        apply Real.sq_sqrt 
        linarith 
      nlinarith [Real.sqrt_nonneg (4 - m)]
    rcases h3 with ⟨x, hx⟩
    specialize h x 
    contradiction 
  have h2 : m - 4 > 0 := by linarith 
  have h3 : m - 3 > 0 := by linarith 
  constructor 
  · exact h2 
  · exact h3