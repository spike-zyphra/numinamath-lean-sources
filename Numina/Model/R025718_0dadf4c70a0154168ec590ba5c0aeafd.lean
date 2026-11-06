import Mathlib

theorem calculus_186763 {f g h : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hh : Differentiable ℝ h) (h0 : f 0 = 1) (h1 : g 0 = 2)
    (h2 : h 0 = 3) (h3 : deriv (fun x => g x * h x) 0 = 4) (h4 : deriv (fun x => h x * f x) 0 = 5)
    (h5 : deriv (fun x => f x * g x) 0 = 6) :
    deriv (fun x => f x * g x * h x) 0 = 16 := by

  have eq1 : deriv (fun x => g x * h x) 0 = deriv g 0 * h 0 + g 0 * deriv h 0 := by
    simp [deriv_mul, hg.differentiableAt, hh.differentiableAt]

  have eq2 : deriv (fun x => h x * f x) 0 = deriv h 0 * f 0 + h 0 * deriv f 0 := by
    simp [deriv_mul, hh.differentiableAt, hf.differentiableAt]

  have eq3 : deriv (fun x => f x * g x) 0 = deriv f 0 * g 0 + f 0 * deriv g 0 := by
    simp [deriv_mul, hf.differentiableAt, hg.differentiableAt]

  have eq4 : deriv (fun x => f x * g x * h x) 0 = deriv f 0 * g 0 * h 0 + f 0 * deriv g 0 * h 0 + f 0 * g 0 * deriv h 0 := by
    simp [deriv_mul, hf.differentiableAt, hg.differentiableAt, hh.differentiableAt]
    all_goals ring

  rw [eq4]
  rw [eq1] at h3
  rw [eq2] at h4
  rw [eq3] at h5

  simp [h0, h1, h2] at h3 h4 h5 ⊢
  linarith