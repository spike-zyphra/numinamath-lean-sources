import Mathlib

/-Compute the range of $y=|x+7|-|x-2|$.-/
theorem algebra_10264 (f : ℝ → ℝ) (hf : f = fun x => abs (x + 7) - abs (x - 2)) :
    Set.range f = {y | -9 ≤ y ∧ y ≤ 9} := by

  apply (Set.range_eq_iff f {y | -9 ≤ y ∧ y ≤ 9}).mpr
  rw [hf]
  simp
  constructor
  . -- ∀x, -9 ≤ |x + 7| - |x - 2| ≤ 9
    intro x
    -- If $x<-7$, both $x+7$ and $x-2$ are negative.
    by_cases h₁: x < -7
    . have : |x + 7| = -(x + 7) := by
        apply abs_of_neg
        linarith
      rw [this]
      have : |x - 2| = -(x - 2) := by
        apply abs_of_neg
        linarith
      rw [this]
      -- So  $$y=-(x+7)-(-x+2)=-9.$$
      simp
      constructor
      . linarith
      . linarith
    -- If $x\geq 2$, both $x+7$ and $x-2$ are nonnegative.
    by_cases h₂: x ≥ 2
    . have : |x + 7| = x + 7 := by
        apply abs_of_nonneg
        linarith
      rw [this]
      have : |x - 2| = x - 2 := by
        apply abs_of_nonneg
        linarith
      rw [this]
      -- So  $$y=(x+7)-(x-2)=9.$$
      simp
      constructor
      . linarith
      . linarith
    -- If $-7\leq x< 2$, $x+7$ is nonnegative and $x-2$ is negative.
    have : |x + 7| = x + 7 := by
      apply abs_of_nonneg
      linarith
    rw [this]
    have : |x - 2| = -(x - 2) := by
      apply abs_of_neg
      linarith
    rw [this]
    -- So  $$y=x+7-(-x+2)=2x+5.$$
    -- Then, $2(-7)+5=-9$, and $2(2)+5=9$.
    -- The function is increasing and continuous, so all values between $-9$ and $9$ are produced, and no others.
    simp
    constructor
    . linarith
    . linarith
  . -- ∀y, y ∈ {y | -9 ≤ y ∧ y ≤ 9} → ∃x, y = |x + 7| - |x - 2|
    intro y hy₁ hy₂
    -- because y = 2x + 5
    use (y - 5) / 2
    have : |(y - 5) / 2 + 7| = (y - 5) / 2 + 7 := by
      apply abs_of_nonneg
      linarith
    rw [this]
    have : |(y - 5) / 2 - 2| = -((y - 5) / 2 - 2) := by
      apply abs_of_nonpos
      linarith
    rw [this]
    linarith
