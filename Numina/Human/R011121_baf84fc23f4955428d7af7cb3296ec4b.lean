import Mathlib
open Real

/- Find the smallest value of $x$ such that $a ≥ 14 √a - x$ for all nonnegtive a. -/
theorem inequalities_611084: 
    IsLeast {x : ℝ | ∀ a : ℝ, a ≥ 0 → a ≥ 14 * √ a - x} 49 := by
  unfold IsLeast
  simp [lowerBounds]
  constructor
  · case left =>
    intro a ha
    -- We have $14 \sqrt{a}-a=49-(\sqrt{a}-7)^{2}$
    have : 14 * √ a - a = 49 - (√ a - 7) ^ 2 := by
      ring_nf
      rw [sq_sqrt ha]
    -- Since (√ a - 7) ^ 2 ≥ 0, we know that $14 \sqrt{a}-a≥49$, which implies $a≥14√a-x$.
    have : 14 * √ a - a ≤ 49 := by 
      simp [this]
      positivity
    linarith
  · case right =>
    -- Then we verify that $x=49$ is the smalleset solution.
    intro a ha
    by_contra! hcx
    have := ha 49
    simp at this
    have htmp : √ 49 = 7 := by 
      apply Real.sqrt_eq_cases.mpr
      simp
      ring
    rw [htmp, show (14 * 7: ℝ) = 98 by ring] at this
    have : a ≥ 49 := by linarith
    have : ¬ a < 49 := by linarith
    contradiction
