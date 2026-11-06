import Mathlib

open Real

theorem calculus_135975 (f : ℝ → ℝ)
    (hf : f = fun x => (2 * x - 1) / (4 * x ^ 2 - 4 * x + 3) +
      (1 / sqrt 2) * arctan ((2 * x - 1) / sqrt 2)) :
    deriv f = fun x => 8 / (4 * x ^ 2 - 4 * x + 3) ^ 2 := by
  rw [hf]
  funext x
  let u := 2 * x - 1
  let v := 4 * x ^ 2 - 4 * x + 3
  let z := (2 * x - 1) / (sqrt 2 : ℝ)

  have h1 : DifferentiableAt ℝ (fun x => 2 * x - 1) x := by
    apply DifferentiableAt.sub
    · -- Show that $2 * x$ is differentiable at $x$
      apply DifferentiableAt.mul
      · -- Show that 2 is differentiable at x
        apply differentiableAt_const
      · -- Show that x is differentiable at x
        apply differentiableAt_id'
    · -- Show that 1 is differentiable at x
      apply differentiableAt_const

  have h2 : DifferentiableAt ℝ (fun x => 4 * x ^ 2 - 4 * x + 3) x := by
    apply DifferentiableAt.add
    · -- DifferentiableAt $4 * x ^ 2 - 4 * x$
      apply DifferentiableAt.sub
      · -- DifferentiableAt $4 * x ^ 2$
        apply DifferentiableAt.mul
        · -- DifferentiableAt 4
          apply differentiableAt_const
        · -- DifferentiableAt x^2
          apply DifferentiableAt.pow
          apply differentiableAt_id'
          all_goals norm_num
      · -- DifferentiableAt $4 * x$
        apply DifferentiableAt.mul
        · -- DifferentiableAt 4
          apply differentiableAt_const
        · -- DifferentiableAt x
          apply differentiableAt_id'
    · -- DifferentiableAt 3
      apply differentiableAt_const

  have h3 : DifferentiableAt ℝ (fun x => (2 * x - 1) / (sqrt 2 : ℝ)) x := by
    apply DifferentiableAt.div
    · -- DifferentiableAt $2*x-1$
      apply DifferentiableAt.sub
      · apply DifferentiableAt.mul
        · apply differentiableAt_const
        · apply differentiableAt_id'
      · apply differentiableAt_const
    · -- DifferentiableAt $sqrt 2$
      apply differentiableAt_const
    all_goals norm_num

  have h5 : sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)

  have h6 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)

  have h7 : 4 * x ^ 2 - 4 * x + 3 ≠ 0 := by 
    nlinarith [sq_nonneg (x - 1 / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  simp [deriv_add, deriv_div, deriv_mul, deriv_id'', mul_comm, mul_assoc, differentiableAt_id', DifferentiableAt.mul, DifferentiableAt.div] at *
  <;> field_simp [h7, h5, h6]
  <;> ring_nf
  <;> norm_num
  <;> ring_nf
  <;> field_simp
  <;> nlinarith [sq_nonneg (x - 1 / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]