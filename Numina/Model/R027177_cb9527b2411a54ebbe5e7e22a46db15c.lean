import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_319445 (a : ℝ) (h : ∀ x, a ≤ x → |x + a| ≥ |x - 3|) :
    a ≥ 1 ∨ a = -3 := by

  -- Apply the hypothesis to x = a
  have h1 := h a (show a ≤ a by linarith)
  cases' abs_cases (a + a) with h2 h2 <;> 
    cases' abs_cases (a - 3) with h3 h3
    <;> try { 
      left; 
      nlinarith
    }
    <;> try { 
      -- Now need to prove a = -3
      have h2 : a ≤ -3 := by nlinarith 
      have h3 := h (-a) (by 
        nlinarith 
      )
      have h4 : |(-a) + a| ≥ |(-a) - 3| := h3 
      have h5 : |(-a) + a| = 0 := by 
        have : (-a) + a = 0 := by linarith 
        rw [this] 
        norm_num 
      have h7 : |(-a) - 3| = 0 := by 
        linarith [h4, h5, abs_nonneg ((-a) - 3)]
      have h8 : (-a) - 3 = 0 := by 
        simpa [abs_eq_zero] using h7 
      right 
      linarith 
    }