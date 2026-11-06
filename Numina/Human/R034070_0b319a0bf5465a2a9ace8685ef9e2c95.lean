import Mathlib

open Real Set
open scoped BigOperators

/- Determine the range of the function $y = \sin x - \sin|x|$. -/
theorem algebra_9210 : range (λ x => sin x - sin (abs x)) = {y | -2 ≤ y ∧ y ≤ 2} := by
  dsimp [Set.range]
  ext y
  constructor <;> intro h
  -- Prove the first direction: range (λ x => sin x - sin (abs x)) ⊆ {y | -2 ≤ y ∧ y ≤ 2}
  · rcases h with ⟨x, hx⟩
    simp; rw [← hx]
    constructor
    -- Using the fact that sin x is in [-1,1], we get the lower bound -2
    · linarith [Real.neg_one_le_sin x, Real.sin_le_one (abs x)]
    -- Similarly, we get the upper bound 2
    · linarith [Real.sin_le_one x, Real.neg_one_le_sin (abs x)]
  -- Prove the second direction: {y | -2 ≤ y ∧ y ≤ 2} ⊆ range (λ x => sin x - sin (abs x))
  · simp_all
    by_cases h : y = 0
    -- When y = 0, we can take x = 0
    · use 0; simp_all
    -- When y ≠ 0, we construct x = arcsin(y/2) - 2π
    · use arcsin (y / 2) - 2 * π
      -- Prove that this x is negative
      have : arcsin (y / 2) - 2 * π < 0 := by
        have := Real.arcsin_le_pi_div_two (y / 2)
        suffices h : arcsin (y / 2) < 2 * π from by linarith
        have h' : π / 2 < 2 * π := by
          conv_rhs => rw [← show π / 2 * 2 = π from div_mul_cancel₀ _ (by norm_num)]
          linarith [pi_pos]
        exact lt_of_le_of_lt this h'
      -- Use the fact that x is negative to simplify abs x
      rw [abs_of_neg this]; simp_all
      -- Prove y/2 is in [-1,1] so that arcsin is well-defined
      have : -1 ≤ y / 2 ∧ y / 2 ≤ 1 := by constructor <;> linarith
      -- Use properties of arcsin to complete the proof
      rw [Real.sin_arcsin this.1 this.2]
      simp_all
