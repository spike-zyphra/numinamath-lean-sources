import Mathlib
open Real

/-
Given: 0 < a < π / 2, tan (α/2) + cot (α/2) = 5/2.
Find the value of sin (α - π/3).
-/
theorem algebra_223455 {α : ℝ}
  (hα : α ∈ Set.Ioo 0 (π/2))
  (tan_cot : tan (α/2) + cot (α/2) = 5/2)
  : sin (α - π/3) = (4 - 3 * √3) / 10
    := by
  -- Get the inequalities from the set definition
  have ⟨ _, _ ⟩ := hα
  -- Calculate the value of sin α
  have h_sin_α : sin α = 4 / 5 := by
    -- Show positivity to enable division
    have : cos (α / 2) > 0 := by
      apply cos_pos_of_mem_Ioo
      simp; constructor <;> linarith
    have : sin (α / 2) > 0 := by
      apply sin_pos_of_mem_Ioo
      simp; constructor <;> linarith
    -- Rewrite tan in terms of sin/cos
    rw [tan_eq_sin_div_cos, cot_eq_cos_div_sin] at tan_cot
    -- Clear fractions, convert multiplication to squares and apply
    -- pythagorean identity
    field_simp [add_comm, <- sq] at tan_cot
    -- Solve for 4 / 5 to substitute later
    have : 4 / 5 = 2 * sin (α / 2) * cos (α / 2) := by
      linear_combination tan_cot * (2 / 5)
    -- Apply double angle identity for sin
    rw [this, <- sin_two_mul]
    ring_nf
  -- Calculate the value of cos α
  have h_cos_α : cos α = 3 / 5 := by
    -- Rewrite cos in terms of sin
    rw [cos_eq_sqrt_one_sub_sin_sq (by linarith) (by linarith)]
    -- Square both sides to get sin^2 α
    apply congrArg (· ^ 2) at h_sin_α
    -- Substitute sin^2 α, and simplify
    rw [h_sin_α, sqrt_eq_cases]
    norm_num
  -- Rewrite sin (α - π / 3)
  calc sin (α - π / 3)
    -- Apply difference formula for sin
    _ = sin α * cos (π / 3) - cos α * sin (π / 3) := by
      rw [sin_sub]
    -- Simplify using known sin/cos values
    _ = sin α * (1/2) - cos α * (√3/2) := by
      simp [cos_pi_div_three, sin_pi_div_three]
    -- Substitute numeric values for sin α and cos α
    _ = (4 - 3 * √3) / 10 := by
      rw [h_sin_α, h_cos_α]
      ring