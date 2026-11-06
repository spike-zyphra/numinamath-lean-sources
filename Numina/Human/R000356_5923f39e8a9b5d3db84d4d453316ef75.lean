import Mathlib
open Real Set

/- Given the function f(x) = e^x - e^-x - 2x, find the solution set for the inequality f(x^2 - 4) + f(3x) > 0. -/
theorem algebra_9112 {f : ℝ → ℝ} (hf : f = λ x => exp x - exp (-x) - 2 * x) :
    {x | f (x ^ 2 - 4) + f (3 * x) > 0} = {x | x > 1 ∨ x < -4} := by

  -- f(x) = e^x - e^-x - 2x is continuous
  have fcont : Continuous f := by
    rw [hf]
    continuity

  -- f'(x) = e^x + e^-x - 2
  have fder x : deriv f x = exp x + exp (-x) - 2 := by
    -- Simplify using the lemmas of deriv
    rw [hf, deriv_sub, deriv_sub, deriv_const_mul, Real.deriv_exp, _root_.deriv_exp, deriv_neg] <;> try simp
    -- Still some "DifferentiableAt" goals left
    . apply DifferentiableAt.neg (by simp)
    . apply DifferentiableAt.exp (DifferentiableAt.neg (by simp))
    . exact DifferentiableAt.exp (DifferentiableAt.neg (by simp))
    . exact DifferentiableAt.mul (by simp) (by simp)

  -- f'(x) = e^x + e^-x - 2 ≥ 0, where the equality holds at x = 0
  have fder1 {x} (hx : x ≠ 0) : deriv f x > 0 := by
    rw [fder, exp_neg]
    field_simp
    -- The goal is now (e^x - 1) ^ 2 > 0
    -- Change it to e^x ≠ 1
    suffices _ : exp x ≠ 1 by nlinarith (config := {splitNe := true})
    contrapose! hx
    rwa [exp_eq_one_iff] at hx

  -- f(x) = e^x - e^-x - 2x is strictly increasing
  have fmono : StrictMono f := by
    -- Suffices to prove that f is strictly increasing on (-∞, 0] and [0, ∞)
    apply StrictMonoOn.Iic_union_Ici (a := 0)
    all_goals
      -- Suffices to prove that f'(x) > 0 for all x in the interior of the interval
      apply strictMonoOn_of_deriv_pos (by
        first | exact convex_Iic 0 | exact convex_Ici 0) (Continuous.continuousOn fcont)
      simp
      intro x hx
      exact fder1 (by linarith)

  ext x
  simp
  -- f is an odd function, we can change "+ f(3x)" to "- f(-3x)", and then use the strict monotonicity of f to change the inequality to -3 * x < x ^ 2 - 4
  conv_lhs =>
    rw [show f (3 * x) = - f (-3 * x) by simp [hf]; ring, ← sub_eq_add_neg, sub_pos, StrictMono.lt_iff_lt fmono]

  -- Quadratic inequality
  constructor <;> intro h <;> contrapose! h
  . nlinarith
  . constructor <;> nlinarith
