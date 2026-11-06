import Mathlib

open Real Set
open scoped BigOperators

/- Determine the interval of monotonic increase for the function $f(x) = e^x - x$. -/
theorem algebra_9171 {f : ℝ → ℝ} (hf : f = λ x => exp x - x) : MonotoneOn f (Set.Ici 0) := by
  -- we can argue f(x) mono by showing its derivative nonneg.
  -- In fact, it is strictmono. so we show mono from strictmono
  -- we calculate the f'(x) first.
  have fderiv: deriv f = (fun x => rexp x - 1) := by
    rw [hf]
    have h1: deriv (fun x => rexp x) = rexp := Real.deriv_exp
    funext x
    have h2: deriv (fun x => (x:ℝ)) x = 1 := by
      apply deriv_id
    have h3: deriv (fun x => rexp x) x = rexp x := by rw [h1]
    rw [← h2, ← h3]
    have hd1: DifferentiableAt ℝ (fun y => y) x := differentiableAt_id'
    have hd2: DifferentiableAt ℝ (fun y => rexp y) x := differentiableAt_exp
    apply deriv_sub hd2 hd1
  -- to use positive derivative to prove strictmono, we should prove f(x) is continuous first.
  have hcont: ContinuousOn f (Ici (0:ℝ)) := by
    rw [hf]
    have h1: ContinuousOn rexp (Ici (0:ℝ)) := continuousOn_exp
    have h2: ContinuousOn (fun x => (x:ℝ)) (Ici (0:ℝ)) := continuousOn_id' (Ici (0:ℝ))
    apply ContinuousOn.sub h1 h2
  have hderivpos: ∀ x ∈ interior (Ici (0:ℝ)), 0 < deriv f x := by
    rw [fderiv]
    intro x hx
    have: interior (Ici (0:ℝ)) = (Ioi (0:ℝ)) := interior_Ici
    rw [this] at hx
    simp at hx
    simp
    exact hx
  have hconv: Convex ℝ (Ici (0:ℝ)) := convex_Ici 0
  have hstrict: StrictMonoOn f (Set.Ici 0) := by
    exact strictMonoOn_of_deriv_pos hconv hcont hderivpos
  exact StrictMonoOn.monotoneOn hstrict