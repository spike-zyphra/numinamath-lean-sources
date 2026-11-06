import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_181383 {f : ℝ → ℝ} (hf : f = λ x => x * (x - 4)^3) :
    Differentiable ℝ f ∧ ∀ x, deriv f x = 0 ↔ x = 4 ∨ x = 1 := by
  constructor
  · -- Show f is differentiable
    rw [hf]
    apply Differentiable.mul
    · exact differentiable_id'
    · -- Show that λ x, (x - 4) ^ 3 is differentiable
      fun_prop
  · -- Show that ∀ x, deriv f x = 0 ↔ x = 4 ∨ x = 1
    intro x
    have h1 : deriv f x = 4 * (x - 4)^2 * (x - 1) := by
      rw [hf]
      simp [deriv_mul, deriv_pow, deriv_id'', mul_comm, mul_assoc]
      all_goals
        ring_nf <;> field_simp <;> ring
    rw [h1]
    constructor
    · -- Forward direction: If f'(x) = 0 then x = 4 or x = 1
      intro h_eq
      cases (mul_eq_zero.mp h_eq) with
      | inl h_eq1 =>
        cases (mul_eq_zero.mp h_eq1) with
        | inl h_eq2 =>
          exfalso
          norm_num at h_eq2
        | inr h_eq3 =>
          left
          nlinarith
      | inr h_eq2 =>
        right
        nlinarith
    · -- Backward direction: If x = 4 or x = 1 then f'(x) = 0
      rintro (h | h)
      · -- x = 4
        rw [h]
        norm_num
      · -- x = 1
        rw [h]
        norm_num