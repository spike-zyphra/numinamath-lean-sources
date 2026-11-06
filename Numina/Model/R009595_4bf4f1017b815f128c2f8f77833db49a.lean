import Mathlib
open Real Set

theorem algebra_9327 {f : ℝ → ℝ} (hf : f = λ x => (3 - x^2) * exp x) :
    StrictMonoOn f (Icc (-3) 1) ∧ StrictAntiOn f (Iic (-3)) ∧ StrictAntiOn f (Ici 1) := by
-- Note on formulation of the problem:
  -- The function is increasing on [-3, 1] and decreasing on (-∞, -3] and [1, ∞)
  -- Thus the interval on which the function is increasing is [-3, 1]

  -- Differentiate the function to determine the monotonicity
  have fder x : deriv f x = (x + 3) * (1 - x) * exp x := by
    -- Use lemmas of differentiation
    rw [hf, deriv_mul, deriv_sub, deriv_pow, Real.deriv_exp] <;> try simp
    . ring
  -- f is continuous by composition of continuous functions
  have fcont : Continuous f := by
    rw [hf]
    continuity

  -- Use the derivative to determine the monotonicity
  refine ⟨?_, ?_, ?_⟩
  . -- f' is positive in the interior of the interval [-3, 1], thus f is strictly increasing on the interval
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (Continuous.continuousOn fcont)
    simp
    intro x hx1 hx2
    rw [fder]
    have h1 : (x + 3) * (1 - x) > 0 := by nlinarith
    nlinarith [exp_pos x]
  . -- f' is negative in the interior of the interval (-∞, -3], thus f is strictly decreasing on the interval
    apply strictAntiOn_of_deriv_neg (convex_Iic _) (Continuous.continuousOn fcont)
    simp
    intro x hx
    rw [fder]
    have h1 : (x + 3) * (1 - x) < 0 := by nlinarith
    nlinarith [exp_pos x]
  . -- f' is negative in the interior of the interval [1, ∞), thus f is strictly decreasing on the interval
    apply strictAntiOn_of_deriv_neg (convex_Ici _) (Continuous.continuousOn fcont)
    simp
    intro x hx
    rw [fder]
    have h1 : (x + 3) * (1 - x) < 0 := by nlinarith
    nlinarith [exp_pos x]