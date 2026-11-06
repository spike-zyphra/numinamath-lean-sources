import Mathlib
open Real Set

/- The monotonically increasing interval of the function $f(x)=|x^{2}-2x-3|$ is $\boxed{\text{answer}}$. -/
theorem algebra_9000 {f : ℝ → ℝ} (hf : f = λ x => abs (x^2 - 2 * x - 3)) :
    MonotoneOn f (Icc (-1) 1) ∧ MonotoneOn f (Ici 3) ∧ AntitoneOn f (Iic (-1)) ∧ AntitoneOn f (Icc 1 3) := by

  -- Rewrite x^2 - 2 * x - 3 as (x - 3) * (x + 1)
  conv at hf =>
    rhs
    ext x
    rw [(by ring : x^2 - 2 * x - 3 = (x - 3) * (x + 1))]

  -- Split the goal into two and simplify the expressions
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro x hx y hy hxy <;> simp [hf, Icc] at * <;> clear hf

  -- When x ≤ y ∈ [-1, 1]
  . -- The expressions in |·| are nonpositive
    have h1 : (x - 3) * (x + 1) ≤ 0 := by nlinarith
    have h2 : (y - 3) * (y + 1) ≤ 0 := by nlinarith
    simp [abs_of_nonpos h1, abs_of_nonpos h2]
    nlinarith

  -- When x ≤ y ∈ [3, ∞)
  . -- The expressions in |·| are nonnegative
    have h1 : (x - 3) * (x + 1) ≥ 0 := by nlinarith
    have h2 : (y - 3) * (y + 1) ≥ 0 := by nlinarith
    simp [abs_of_nonneg h1, abs_of_nonneg h2]
    nlinarith

  . -- When x ≤ y ∈ (-∞, -1]
    have h1 : (x - 3) * (x + 1) ≥ 0 := by nlinarith
    have h2 : (y - 3) * (y + 1) ≥ 0 := by nlinarith
    simp [abs_of_nonneg h1, abs_of_nonneg h2]
    nlinarith

  . -- When x ≤ y ∈ [1, 3]
    have h1 : (x - 3) * (x + 1) ≤ 0 := by nlinarith
    have h2 : (y - 3) * (y + 1) ≤ 0 := by nlinarith
    simp [abs_of_nonpos h1, abs_of_nonpos h2]
    nlinarith
