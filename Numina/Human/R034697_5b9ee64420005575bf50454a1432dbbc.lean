import Mathlib

/- If b and c are constants and (x+2)(x+b)=x^2+c*x+6, then c is
(A) −5 (B) −3 (C) −1 (D) 3 (E) 5-/
theorem algebra_96353 {b c : ℝ} (h : ∀ x, (x + 2) * (x + b) = x ^ 2 + c * x + 6) : c = 5 := by {
  -- Evaluate both sides at -2. This makes the left-hand side vanish and thus gives us a linear equation for c.
  have hm2 := h (-2)
  -- Simplify that equation
  ring_nf at hm2
  -- Solve for c.
  calc c = - (10 - c * 2) / 2 + 5 := by ring
       _ = 5 := by rw [←hm2]; norm_num
}