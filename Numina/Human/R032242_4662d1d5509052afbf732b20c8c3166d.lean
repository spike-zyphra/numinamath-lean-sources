import Mathlib


/-Suppose the function $f(x)-f(2 x)$ has derivative 5 at $x=1$ and derivative 7 at $x=2$.
Find the derivative of $f(x)-f(4 x)$ at $x=1$.-/
theorem calculus_611202 (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hd1 : deriv (fun x ↦ f x - f (2 * x)) 1 = 5)
    (hd2 : deriv (fun x ↦ f x - f (2 * x)) 2 = 7) :
    deriv (fun x ↦ f x - f (4 * x)) 1 = 19 := by
  let g := fun x ↦ f x - f (2 * x) --  Let $g(x)=f(x)-f(2 x)$.
  have hd3 : Differentiable ℝ (fun y : ℝ ↦ 2 * y) := by
    apply Differentiable.const_mul
    exact differentiable_id'
  have hg : Differentiable ℝ g := by
    unfold g
    apply Differentiable.sub hf
    apply Differentiable.comp hf hd3
  have hg2 : Differentiable ℝ (fun x ↦ g (2 * x)) := by
    apply Differentiable.comp hg hd3
  have hgf : (fun x ↦ f x - f (4 * x)) = fun x ↦ g x + g (2 * x) := by 
    -- Then we want the derivative of $$ f(x)-f(4 x)=(f(x)-f(2 x))+(f(2 x)-f(4 x))=g(x)+g(2 x) $$ at $x=1$.
    ext x
    simp [g]
    ring_nf
  have h (x : ℝ) : deriv (fun x ↦ g x + g (2 * x)) x = deriv g x + 2 * deriv g (2 * x) := by
   -- This is $g^{\prime}(x)+2 g^{\prime}(2 x)$ at $x=1$,
    rw [deriv_add (hg x) (hg2 x)]
    rw [show (fun x ↦ g (2 * x)) = g ∘ (fun x ↦ 2 * x) by ext ; simp]
    rw [deriv_comp, deriv_const_mul]
    simp only [deriv_id'', mul_one, add_right_inj]
    rw [mul_comm]
    · exact differentiableAt_id'
    · exact hg (2 * x)
    · exact hd3 x
  simp only [hgf, h, mul_one]
  rw [hd1, hd2]
  -- or $5+2 \cdot 7=19$.
  norm_num
