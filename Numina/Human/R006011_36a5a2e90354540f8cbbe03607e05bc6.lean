import Mathlib 

open Real 
/- A particle moves along the $x$-axis in such a way that its velocity at position $x$ is 
given by the formula $v(x)=2+\sin x$. 
What is its acceleration at $x=\frac{\pi}{6}$ ?-/
theorem calculus_611095 (a t : ℝ) (v x : ℝ → ℝ) (hx : Differentiable ℝ x) 
    (hv : v = fun t ↦ 2 + (sin ∘ x) t) (ha : a = deriv v t) 
    (hxv : deriv x = v) (hxt : x t = π / 6) :
    a = 5 * √ 3 / 4 := by 
  simp only [ha, hv, differentiableAt_const, deriv_const_add'] 
  rw [deriv_comp] 
  -- Acceleration is given by 
  -- $a=\frac{d v}{d t}=\frac{d v}{d x} \cdot \frac{d x}{d t}
  · simp [hxt, hxv, hv] 
    ring 
    -- =\frac{d v}{d x} \cdot v=\cos x \cdot(2+\sin x)=5 \sqrt{3} / 4$.
  · exact differentiableAt_sin
  · exact hx t