import Mathlib


/- The function $f(x)$ satisfies the equation $2f(x)+f(-x)=2x$. Find $f(x)$. -/
theorem algebra_9250 {f : ℝ → ℝ} (h : ∀ x, 2 * f x + f (-x) = 2 * x) :
    ∀ x, f x = 2 * x := by
    intro x
    -- Given $2f(x)+f(-x)=2x$, $(1)$
    have hx := h x; simp at hx
    -- Substitute $x$ with $-x$ to get $2f(-x)+f(x)=-2x$, $(2)$
    have hmx := h (-x); simp at hmx
    -- Eliminating $f(-x)$ from equations $(1)$ and $(2)$, we get $3f(x)=6x$,
    have e := congrArg (fun t => t - (2 * f x)) hx; simp at e
    rw [e] at hmx;
    ring_nf at hmx
    have res := congrArg (fun t => t + (f x * 3) + (x * 2)) hmx; ring_nf at res
    symm at res
    have res2 := congrArg (fun t => t / 3) res; ring_nf at res2
    rw [mul_comm]
    -- Therefore, $f(x)=2x$. So, the final answer is $\boxed{f(x)=2x}$.
    exact res2
