import Mathlib

-- Define the quadratic function
def f_9158 (x : ℝ) : ℝ := x^2 - 4*x - 5

-- Define the factored form
def g_9158 (x : ℝ) : ℝ := (x - 5) * (x + 1)

/-Solve the quadratic equation: $x^{2}-4x-5=0$.-/
theorem algebra_9158 (x : ℝ) :
  f_9158 x = 0 ↔ x = 5 ∨ x = -1 := by
  -- x = -1 is a solution
  have solution_neg_one : f_9158 (-1) = 0 := by
    unfold f_9158
    norm_num
  -- x = 5 is a solution
  have solution_five: f_9158 5 = 0 := by
    unfold f_9158
    norm_num
  constructor
  · intro h
    -- The original and factored forms are equivalent
    have equiv_forms : ∀ (x : ℝ), f_9158 x = g_9158 x := by
      intro x
      unfold f_9158 g_9158
      ring
    rw [equiv_forms] at h
    unfold g_9158 at h
    have h2 : (x - 5) = 0 ∨ (x + 1) = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h
    cases h2 with
    | inl h3 => -- Case x - 5 = 0
      left
      exact sub_eq_zero.mp h3
    | inr h3 => -- Case x + 1 = 0
      right
      exact Eq.symm (neg_eq_of_add_eq_zero_left h3)
  · intro h
    cases h with
    | inl h1 => -- Case x = 5
      rw [h1]
      exact solution_five
    | inr h1 => -- Case x = -1
      rw [h1]
      exact solution_neg_one
