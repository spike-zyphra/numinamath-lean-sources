import Mathlib

open Real
/-Find the value of $6+\frac{1}{2+\frac{1}{6+\frac{1}{2+\frac{1}{6+\cdots}}}}$. Your answer will be of the form $a+b\sqrt{c}$ where no factor of $c$ (other than $1$) is a square. Find $a+b+c$.-/
theorem algebra_20104 {x : ℝ} (hx : x = 6 + 1 / (2 + 1 / x)) (hx1 : 6 < x):
    ∃ a b c, Squarefree c ∧ c > 0 ∧ x = a + b * sqrt c ∧ a + b + c = 8 := by
    --Let $x=6+\frac{1}{2+\frac{1}{6+\frac{1}{2+\frac{1}{6+\cdots}}}}$. Then we have $x=6+\frac{1}{2+\frac{1}{x}}$.
     have e :=  congrArg ( fun (t) => ((t) - 6) * (2 + 1 / x)) hx; beta_reduce at e
     rw [show (6 + 1 / (2 + 1 / x) - 6) * (2 + 1 / x) = (2 + 1 / x) / (2 + 1 / x) by ring_nf] at e; rw [div_self] at e
     --This means $x-6=\frac{1}{2+\frac{1}{x}}$ or $(x-6)\left(2+\frac{1}{x}\right)=1$.
     rw [show  (x - 6) * (2 + 1 / x) = 2 * x - 12 + x / x -  6 / x by ring_nf] at e; rw [div_self] at e
     --Expanding the product gives $2x-12+1-\frac{6}{x}=1$, or $2x-12-\frac{6}{x}=0$.
     have e2 :=  congrArg ( fun (t) => ((t) - 1) *  x / 2) e; beta_reduce at e2
     rw [show  (2 * x - 12 + 1 - 6 / x - 1) * x / 2  = x*x - 6*x - 6 / 2 * (x / x) by ring_nf] at e2; rw [div_self] at e2; ring_nf at e2
     -- Multiply through by $x$ and divide by $2$ to find $x^2-6x-3=0$.
     rw [show -3 - x * 6 + x ^ 2 = 1 * (x * x) + (-6) * x + (-3) by ring_nf] at e2
     --Using the quadratic formula, we find $x=\frac{6\pm\sqrt{(-6)^2-4(-3)(1)}}{2(1)}=\frac{6\pm\sqrt{48}}{2}=3\pm2\sqrt{3}$.
     have  ha : (1 : ℝ) ≠ 0 := by simp
     have  hdis :  discrim (1 : ℝ) (-6) (-3) =  (4 * √3) * (4 * √3)  := by
       rw [discrim]; ring_nf
       rw [Real.sq_sqrt]; ring_nf
       linarith
     rw[quadratic_eq_zero_iff ha hdis] at e2
     --Discuss two roots separately
     cases e2 with
     | inl h =>
       -- Looking at the original expression for $x$, we can see that it is greater than $6$.
       simp at h ;ring_nf at h
       --So we take the positive value $3+2\sqrt{3}$ and get $a+b+c=3+2+3=\boxed{8}$.
       use 3 ,2,3
       norm_num
       ring_nf
       exact h
     | inr h =>
       simp at h
       --Another root is less than 6
       have e2 := congrArg ( fun (t) => ((t) * 2)) h ; beta_reduce at e2; ring_nf at e2
       have hlt : 6 - √3 * 4 < 0 := by
         simp
         have heq :  (6 : ℝ) ^ 2 < 48 := by linarith
         have heq2 : √3 * 4 = √48 := by
           have hsqrt16 : 4 = √(4 ^ 2) := by
             rw [Real.sqrt_sq_eq_abs]
             simp
           rw [hsqrt16]
           ring_nf
           have h : (0 : ℝ) ≤ 3 := by linarith
           have h2 :=  Real.sqrt_mul h 16
           rw [← h2]; ring_nf
         rw [heq2]
         apply Real.lt_sqrt_of_sq_lt heq
       linarith
     --Validate inequality
     nlinarith;nlinarith
     have hx3 : 0 < 1 / x  := by
       simp
       linarith
     linarith