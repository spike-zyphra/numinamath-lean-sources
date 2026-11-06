import Mathlib

theorem algebra_13931 :
    {x : ℝ | (x - 5 * x + 12) ^ 2 + 1 = - |x|}.encard = 0 := by 
  have h : ∀ (x : ℝ), ¬ ((x - 5 * x + 12) ^ 2 + 1 = - |x|) := by
    intro x 
    intro hx 
    have h1 : (x - 5 * x + 12) ^ 2 ≥ 0 := by 
      apply sq_nonneg 
    have h2 : (x - 5 * x + 12) ^ 2 + 1 ≥ 1 := by 
      linarith 
    have h3 : -|x| ≤ 0 := by 
      linarith [abs_nonneg x]
    linarith 
  have h' : {x : ℝ | (x - 5 * x + 12) ^ 2 + 1 = - |x|} = ∅ := by 
    ext x 
    simp [h]
  rw [h']
  simp