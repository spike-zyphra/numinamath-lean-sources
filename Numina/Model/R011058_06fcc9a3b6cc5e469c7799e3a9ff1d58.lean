import Mathlib 

theorem calculus_610982 (f g h : ℝ → ℝ) (df : Differentiable ℝ f) (dg : Differentiable ℝ g) (dh : Differentiable ℝ h) 
    (hf : f 0 = 1) (hg : g 0 = 2) (hh : h 0 = 3) (hgh : deriv (fun x ↦ g x * h x) 0 = 4) 
    (hhf : deriv (fun x ↦ h x * f x) 0 = 5) (hfg : deriv (fun x ↦ f x * g x) 0 = 6) : 
    deriv (fun x ↦ f x * g x * h x) 0 = 16 := by
  have eq1 : deriv (fun x ↦ g x * h x) 0 = (deriv g 0) * (h 0) + (g 0) * (deriv h 0) := by 
    simp [deriv_mul, hg, hh, differentiableAt_id', dg 0, dh 0]
    <;> ring_nf <;> simp [hg, hh] 
    <;> ring
  rw [hgh] at eq1
  rw [hg, hh] at eq1
  -- eq1 now: 4 = 3 * (deriv g 0) + 2 * (deriv h 0)
  have eq2 : deriv (fun x ↦ h x * f x) 0 = (deriv h 0) * (f 0) + (h 0) * (deriv f 0) := by 
    simp [deriv_mul, hh, hf, differentiableAt_id', dh 0, df 0]
    <;> ring_nf <;> simp [hh, hf]
    <;> ring
  rw [hhf] at eq2
  rw [hf, hh] at eq2
  -- eq2 now: 5 = 1 * (deriv h 0) + 3 * (deriv f 0)
  have eq3 : deriv (fun x ↦ f x * g x) 0 = (deriv f 0) * (g 0) + (f 0) * (deriv g 0) := by 
    simp [deriv_mul, hf, hg, differentiableAt_id', df 0, dg 0]
    <;> ring_nf <;> simp [hf, hg]
    <;> ring
  rw [hfg] at eq3
  rw [hf, hg] at eq3
  -- eq3 now: 6 = 2 * (deriv f 0) + 1 * (deriv g 0)
  have eq4 : deriv (fun x ↦ f x * g x * h x) 0 = (deriv f 0) * (g 0) * (h 0) + (f 0) * (deriv g 0) * (h 0) + (f 0) * (g 0) * (deriv h 0) := by 
    simp [deriv_mul, hf, hg, hh, differentiableAt_id', df 0, dg 0, dh 0, mul_assoc]
    <;> ring_nf <;> simp [hf, hg, hh, mul_assoc]
    <;> ring
  rw [eq4]
  rw [hf, hg, hh]
  -- eq4 now has variables and derivatives substituted
  have h1 : deriv f 0 = 2 := by
    nlinarith [eq1, eq2, eq3]
  -- Solving derivatives using system of equations
  have h2 : deriv g 0 = 2 := by
    nlinarith [eq1, eq2, eq3]
  -- Solving derivatives using system of equations
  have h3 : deriv h 0 = -1 := by
    nlinarith [eq1, eq2, eq3]
  rw [h1, h2, h3]
  norm_num