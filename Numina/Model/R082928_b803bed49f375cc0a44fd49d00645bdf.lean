import Mathlib

theorem algebra_220964 :
    (∀ x : ℝ, ⌊x + 1⌋ = ⌊x⌋ + 1) ∧ ¬(∀ x y : ℝ, ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋) ∧
    ¬(∀ x y : ℝ, ⌊x * y⌋ = ⌊x⌋ * ⌊y⌋) := by
  constructor
  · intro x
    simp
  constructor
  · -- Statement II is false, we provide a counterexample.
    push_neg
    use 0.5, 0.5
    norm_num
  · -- Statement III is false, we provide a counterexample.
    push_neg
    use 2.5, 0.4
    norm_num