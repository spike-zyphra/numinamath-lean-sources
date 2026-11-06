import Mathlib

/- Given $x^{2}+\left(2-a\right)x+4-2a \gt 0$, which holds true for all $x\in \left[2,+\infty \right)$, the range of real number $a$ is ______. -/
theorem algebra_9357 (a : ℝ) :
    (∀ x ∈ Set.Ici 2, x^2 + (2 - a)*x + 4 - 2*a > 0) ↔ a < 3 := by
  -- Simplify the hypothesis
  simp
  -- Split the goal into two
  constructor <;> intro h
  . -- Let x = 2
    specialize h 2 (by norm_num)
    linarith
  . intro x hx
    suffices : (x + 2) * a < x^2 + 2*x + 4; linarith
    -- Simple calculation
    calc (x + 2) * a < (x + 2) * 3 := by nlinarith
                   _ ≤ (x + 2) * 3 + (x + 1) * (x - 2) := by nlinarith
                   _ = x^2 + 2*x + 4 := by ring
