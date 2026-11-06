import Mathlib

/- A line parallel to $3x-7y = 65$ passes through the point $(7,4)$ and $(0,K)$. What is the value of K?-/

theorem algebra_19253 (K : ℝ) (h : m = - 3 / - 7 ) (h2 : (4- K) / (7 - 0) = m ):

    K = 1 := by
    --We put the equation of the line into slope-intercept form by solving for $y$: $y=\frac{65-3x}{-7}$. That means the slope of the line is $\frac{3}{7}$, and the slope of a parallel line must also be $\frac{3}{7}$.
    ring_nf at h
    rw [h] at h2
    --The slope of the line through $(7,4)$ and $(0,K)$ is $\frac{4-K}{7-0}$, which we set equal to $\frac{3}{7}$ and solve for $K$. $$\frac{4-K}{7}=\frac{3}{7}\qquad\Rightarrow 4-K=3 \qquad\Rightarrow 1=K$$ So the value of K is $\boxed{1}$.
    simp at h2
    have e:= congrArg (fun (t) => (t) * 7 + K -3) h2; beta_reduce at e; ring_nf at e
    rw [e]
