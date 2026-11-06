import Mathlib

open Real Set
open scoped BigOperators

/- Determine the interval of increase for the function $y = x - e^x$. -/
theorem algebra_9051 {f : ℝ → ℝ} (hf : f = λ x => x - exp x) : StrictMonoOn f {x | x < 0} := by
  -- we argue f(x) strictmono by showing its derivative positive.
  -- so, we calculate the f'(x) first.
  have fderiv: deriv f = (fun x => 1 - rexp x) := by
    rw [hf]
    have h1: deriv (fun x => rexp x) = rexp := Real.deriv_exp
    funext x
    have h2: deriv (fun x => (x:ℝ)) x = 1 := by
      apply deriv_id
    have h3: deriv (fun x => rexp x) x = rexp x := by rw [h1]
    rw [← h2, ← h3]
    have hd1: DifferentiableAt ℝ (fun y => y) x := differentiableAt_id'
    have hd2: DifferentiableAt ℝ (fun y => rexp y) x := differentiableAt_exp
    apply deriv_sub hd1 hd2
  -- to use positive derivative to prove strictmono, we should prove f(x) is continuous first.
  have h1: {x|x<0} = Iio (0:ℝ) := by
        ext y
        simp
  have hcont: ContinuousOn f {x | x < 0} := by
    rw [hf]
    have h1: ContinuousOn (fun x => (x:ℝ)) {x | x<0} := continuousOn_id' {x | x < 0}
    have h2: ContinuousOn rexp {x|x<0} := continuousOn_exp
    apply ContinuousOn.sub h1 h2
  have hderivpos: ∀ x ∈ interior {x | x < 0}, 0 < deriv f x := by
    rw [fderiv]
    intro x hx
    have: interior {x|x<0} = Iio (0:ℝ) := by
      rw [h1]
      exact interior_Iio
    rw [this] at hx
    simp at hx
    simp
    exact hx
  have hconv: Convex ℝ {x | x < (0:ℝ)} := by
    rw [h1]
    exact convex_Iio 0
  apply strictMonoOn_of_deriv_pos hconv hcont hderivpos