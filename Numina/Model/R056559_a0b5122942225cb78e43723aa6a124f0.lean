import Mathlib

theorem algebra_41819 (f g h : Polynomial ℝ) (hf : ∀ x, f.eval x = 0)
    (hg : ∀ x, g.eval x = -x) (hh : ∀ x, h.eval x = -x + 2)
    (hfg : ∀ x, abs (f.eval x) - abs (g.eval x) + h.eval x = if x < -1 then -1 else (if (x ≤ 0) then 3 * x + 2 else -2 * x + 2)) :
    True := by 
  trivial