import Mathlib

open Real

theorem algebra_266535 {a : ℕ → ℝ} (ha1 : a 1 = 0) (han : ∀ n ≥ 1, a (n + 1) = a n + 1 + 2 * sqrt (1 + a n)) :
    a 2009 = 4036080 := by

  have h1 : ∀ (n : ℕ), a (n + 1) = ((n + 1 : ℝ) ) ^ 2 - 1 := by 
    intro n 
    induction n with 
    | zero =>
      rw [ha1]
      norm_num 
    | succ n ih =>
      have h2 : a (n + 2) = a (n + 1) + 1 + 2 * sqrt (1 + a (n + 1)) := by
        specialize han (n + 1) (by linarith)
        simpa using han
      have eq1 : sqrt (1 + a (n + 1)) = (n + 1 : ℝ) := by 
        have eq2 : 1 + a (n + 1) = ((n + 1 : ℝ) ) ^ 2 := by 
          have eq3 : a (n + 1) = (n + 1 : ℝ) ^ 2 - 1 := by 
            simpa using ih 
          rw [eq3]
          all_goals nlinarith 
        rw [eq2]
        have h6 : sqrt (((n + 1 : ℝ) ) ^ 2) = (n + 1 : ℝ) := by 
          rw [Real.sqrt_sq (by positivity)]
        rw [h6]
      have eq3 : a (n + 1) = (n + 1 : ℝ) ^ 2 - 1 := by 
        simpa using ih 
      rw [h2] 
      rw [eq1]
      rw [eq3]
      field_simp at *
      <;> nlinarith 
  have h2008 := h1 2008
  norm_num at h2008 ⊢
  linarith