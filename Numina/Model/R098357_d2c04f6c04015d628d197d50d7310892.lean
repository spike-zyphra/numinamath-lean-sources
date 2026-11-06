import Mathlib

open Real

theorem inequalities_208697 (x : ℝ) (hx : 1 - x > (1 - x)^2 ∧ (1 - x)^2 > (1 - x)^3 ∧ (1 - x)^3 > (1 - x)^4) :
    0 < x ∧ x < 1 := by
  have h1 : 1 - x > (1 - x)^2 := hx.1
  have h2 : (1 - x)^2 > (1 - x)^3 := hx.2.1
  have h3 : (1 - x)^3 > (1 - x)^4 := hx.2.2
  
  -- From h1: 1 - x > (1 - x)^2
  -- This can be rewritten as (1 - x)^2 - (1 - x) < 0
  -- Factor: (1 - x)(1 - x - 1) < 0
  -- Simplify: (1 - x)(-x) < 0
  -- This becomes (1 - x)x > 0.
  
  have h4 : 0 < 1 - x := by
    nlinarith [h1, h2]
  
  -- Now that we have h4: 1 - x > 0, so x < 1
  
  have h5 : 0 < x := by
    nlinarith [h1, h4]
  
  -- Now that we have h5: 0 < x
  
  have h6 : x < 1 := by
    nlinarith [h4]
  
  exact ⟨h5, h6⟩