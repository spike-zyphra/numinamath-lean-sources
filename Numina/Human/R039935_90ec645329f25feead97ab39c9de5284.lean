import Mathlib

open Real

/- A steam boiler consists of a cylinder that ends in a hemisphere at each end. If the length and width of the cylinder are changed so that the total length of the boiler remains constant, the question is, what dimensions of the cylinder will maximize the volume of the boiler? -/
theorem calculus_268354 {l : ℝ} {V : ℝ → ℝ} (hl : l > 0)
  (hV : V = fun x ↦ π / 12 * (x / 2)^2 * (3 * l - x)) :
  IsMaxOn V (Set.Icc 0 l) l := by
  -- V is monotone on the interval [0, l]
  have mono_V : MonotoneOn V (Set.Icc 0 l)
  -- equivalently, the derivative of V is nonnegative on [0, l]
  · apply monotoneOn_of_deriv_nonneg (convex_Icc 0 l)
    all_goals rw [hV]
    -- V is continuous on [0, l]
    · apply ContinuousOn.mul
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.pow
      apply ContinuousOn.div_const (continuousOn_id' _)
      exact ContinuousOn.sub continuousOn_const (continuousOn_id' _)
    -- V is differentiable on [0, l]
    · apply DifferentiableOn.mul
      apply DifferentiableOn.mul
      apply differentiableOn_const
      apply DifferentiableOn.pow
      apply DifferentiableOn.div_const differentiableOn_id'
      exact DifferentiableOn.sub (differentiableOn_const _) differentiableOn_id'
    -- V is differentiable at x
    · intro x hx
      rw [deriv_mul, deriv_sub]
      simp
      simp only [interior_Icc, Set.mem_Ioo] at hx
      rw [mul_assoc, mul_le_mul_iff_of_pos_left (show 0 < π / 12 by linarith [pi_pos])]
      nlinarith
      exact differentiableAt_const _
      exact differentiableAt_id'
      apply DifferentiableAt.const_mul
      apply DifferentiableAt.pow
      apply DifferentiableAt.div_const
      exact differentiableAt_id'
      apply DifferentiableAt.sub (differentiableAt_const _)
      exact differentiableAt_id'
  -- conclude
  rw [isMaxOn_iff]
  intro x hx
  apply mono_V hx _ (Set.mem_Icc.mp hx).right
  simp only [Set.mem_Icc, le_refl, and_true]
  exact hl.le