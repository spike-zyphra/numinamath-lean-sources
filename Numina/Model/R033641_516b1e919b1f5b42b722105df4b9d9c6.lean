import Mathlib

theorem algebra_9057
    {f : ℝ → ℝ}
    {m : ℝ}
    (hfp : m ^ 2 - 5 * m + 7 = 1)
    (hf : f = fun x => (m ^ 2 - 5 * m + 7) * x ^ (m - 2)) :
    (∀ x, f (-x) = - f x ) ↔ m = 3 := by
  have heq : m ^ 2 - 5 * m + 6 = 0 := by
    nlinarith 
  have h1 : (m - 2) * (m - 3) = 0 := by
    nlinarith [heq]
  constructor
  · -- Assume $f$ is odd, prove $m = 3$.
    intro h
    have eq2 := h 1
    simp [hf] at eq2
    rw [hfp] at eq2
    have eq3 := h (-1)
    simp [hf] at eq3
    rw [hfp] at eq3 
    have h2 : m = 2 ∨ m = 3 := by
      cases (mul_eq_zero.1 h1) with
      | inl h => 
        left 
        linarith 
      | inr h => 
        right 
        linarith 
    rcases h2 with (h2 | h2)
    · -- Assume m = 2 
      rw [show m = (2 : ℝ) by linarith [h2]] at eq3
      norm_num at eq3 
    · -- Assume m = 3 
      linarith [h2]
  · -- Assume m = 3 
    intro h0
    intro x 
    rw [hf]
    rw [show m = (3 : ℝ) by linarith [h0]]
    all_goals 
      norm_num [h0] 
      <;> ring_nf