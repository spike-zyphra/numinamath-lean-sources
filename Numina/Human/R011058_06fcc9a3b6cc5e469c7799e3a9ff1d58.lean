import Mathlib 

/- We are given the values of the differentiable real functions $f, g, h$, as well as the derivatives of their pairwise products, at $x=0$ :
$$
f(0)=1 ; g(0)=2 ; h(0)=3 ; \quad(g h)^{\prime}(0)=4 ; \quad(h f)^{\prime}(0)=5 ; \quad(f g)^{\prime}(0)=6 .
$$
Find the value of $(f g h)^{\prime}(0)$. -/
theorem calculus_610982 (f g h : ℝ → ℝ) (df : Differentiable ℝ f) (dg : Differentiable ℝ g) (dh : Differentiable ℝ h) 
    (hf : f 0 = 1) (hg : g 0 = 2) (hh : h 0 = 3) (hgh : deriv (fun x ↦ g x * h x) 0 = 4) 
    (hhf : deriv (fun x ↦ h x * f x) 0 = 5) (hfg : deriv (fun x ↦ f x * g x) 0 = 6) : 
    deriv (fun x ↦ f x * g x * h x) 0 = 16 := by 
  rw [← mul_right_inj' (by norm_num : (2 : ℝ) ≠ 0)] 
  calc 
    _ = 2 * (deriv f 0 * g 0 * h 0 + f 0 * deriv g 0 * h 0 + f 0 * g 0 * deriv h 0) := by 
      rw [deriv_mul, deriv_mul] ; ring   
      · exact df 0
      · exact dg 0
      · exact DifferentiableAt.mul (df 0) (dg 0)
      · exact dh 0 
    -- By the product rule, $(f g h)^{\prime}=f^{\prime} g h+f g^{\prime} h+f g h^{\prime}
    _ = deriv (fun x ↦ f x * g x) 0 * h 0 + deriv (fun x ↦ g x * h x) 0 * f 0 
      + deriv (fun x ↦ h x * f x) 0 * g 0 := by 
      rw [deriv_mul (df 0) (dg 0), deriv_mul (dg 0) (dh 0), deriv_mul (dh 0) (df 0)] 
      ring 
    -- = \left((f g)^{\prime} h+(g h)^{\prime} f+\right.$ $\left.(h f)^{\prime} g\right) 
    -- Evaluated at 0 , this gives 16.
    _ = 2 * 16 := by rw [hf, hg, hh, hgh, hhf, hfg] ; ring  




 