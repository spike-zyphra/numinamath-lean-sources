import Mathlib

open Real Set
open scoped Real

theorem algebra_323520 (α : ℝ) :
    ∃ θ : ℝ, Real.cos θ - Real.sin θ ^ 2 = α ↔ -5 / 4 ≤ α ∧ α ≤ 1 := by 
  by_cases h1 : -5 / 4 ≤ α
  · -- Assume $-5/4 \leq \alpha$
    by_cases h2 : α ≤ 1
    · -- Assume $-5/4 \leq \alpha \land \alpha \leq 1$
      use Real.arccos ((-1 + Real.sqrt (4 * α + 5)) / 2)
      constructor
      · -- Forward: if the equation holds, then $-5/4 \leq \alpha \land \alpha \leq 1$
        intro h
        constructor <;> nlinarith [Real.sqrt_nonneg (4 * α + 5), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * α + 5 by nlinarith)]
      · -- Backward: if $-5/4 \leq \alpha \land \alpha \leq 1$, then the equation holds
        intro h
        have h5 : Real.cos (Real.arccos ((-1 + Real.sqrt (4 * α + 5)) / 2)) = ((-1 + Real.sqrt (4 * α + 5)) / 2) := by
          apply Real.cos_arccos
          · -- Show that -1 ≤ (-1 + sqrt(4*α + 5)) / 2
            nlinarith [Real.sqrt_nonneg (4 * α + 5), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * α + 5 by nlinarith)]
          · -- Show that (-1 + sqrt(4*α + 5)) / 2 ≤ 1
            nlinarith [Real.sqrt_nonneg (4 * α + 5), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * α + 5 by nlinarith)]
        have h6 : Real.sin (Real.arccos ((-1 + Real.sqrt (4 * α + 5)) / 2)) ^ 2 = 1 - Real.cos (Real.arccos ((-1 + Real.sqrt (4 * α + 5)) / 2)) ^ 2 := by 
          rw [Real.sin_sq]
        nlinarith [Real.sqrt_nonneg (4 * α + 5), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * α + 5 by nlinarith)]
    · -- Assume $-5/4 \leq \alpha$ but not $\alpha \leq 1$
      use 0
      constructor
      · -- Forward
        intro h
        nlinarith [Real.sin_zero, Real.cos_zero]
      · -- Backward
        intro h
        linarith
  · -- Assume not $-5/4 \leq \alpha$
    use 0
    constructor
    · -- Forward
      intro h
      nlinarith [Real.sin_zero, Real.cos_zero]
    · -- Backward
      intro h
      linarith