import Mathlib

theorem algebra_5651 {p : Polynomial ℝ} :
    (∀ x : ℝ, Real.sin (p.eval x) < p.eval x) ↔ ∀ x : ℝ, p.eval x > 0 := by 
  constructor
  · -- Assume h : ∀ x : ℝ, Real.sin (p.eval x) < p.eval x, prove ∀ x : ℝ, p.eval x > 0
    intro h
    intro x 
    by_cases h5 : p.eval x ≤ 0
    · -- Assume p.eval x ≤ 0, show a contradiction
      have hx4 : p.eval x ≤ 0 := h5
      have h5 : Real.sin (p.eval x) ≥ p.eval x := by
        have hx5 : 0 ≤ (- p.eval x) := by linarith
        have h6 : Real.sin (- p.eval x) ≤ (- p.eval x) := by 
          apply Real.sin_le 
          all_goals linarith
        have h7 : Real.sin (- p.eval x) = - Real.sin (p.eval x) := by 
          rw [Real.sin_neg]
        have h8 : - Real.sin (p.eval x) ≤ - p.eval x := by linarith 
        linarith 
      -- We know Real.sin (p.eval x) < p.eval x from h
      have h2 : Real.sin (p.eval x) < p.eval x := h x 
      -- contradiction Real.sin (p.eval x) < p.eval x and Real.sin (p.eval x) ≥ p.eval x 
      linarith
    · -- p.eval x > 0 
      have h5 : p.eval x > 0 := by linarith 
      linarith 
  · -- Backward implication: Assume ∀ x : ℝ, p.eval x > 0, prove ∀ x : ℝ, Real.sin (p.eval x) < p.eval x 
    intro hp 
    intro x 
    have hp3 : p.eval x > 0 := hp x
    have h3 : Real.sin (p.eval x) < p.eval x := by 
      have h4 : p.eval x > 0 := hp3 
      have h5 : Real.sin (p.eval x) < p.eval x := by 
        have h6 : p.eval x > 0 := h4 
        have h7 : Real.sin (p.eval x) < p.eval x := by 
          have h5a : Real.sin (p.eval x) < p.eval x := by 
            apply Real.sin_lt 
            all_goals linarith 
          linarith 
        linarith 
      linarith 
    linarith