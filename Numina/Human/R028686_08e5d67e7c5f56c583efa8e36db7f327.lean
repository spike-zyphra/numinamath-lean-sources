import Mathlib
/- ## Task 1.

Determine all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that for all real numbers $x$ and $y$,

$$
x f(x) - y f(y) = (x - y)(f(x + y) - xy)
$$ -/
theorem algebra_248374 {f : ℝ → ℝ} : (∀ x y, x * f x - y * f y = (x - y) * (f (x + y) - x * y)) ↔
∃ b c, ∀ x, f x = x ^ 2 + b * x +c:= by
  -- Split the proof into two directions: forward and reverse implications
  constructor
  -- Forward direction: if f satisfies the functional equation, then f is a quadratic function
  .
    intro h
    -- We'll use f(1) and f(-1) to determine the coefficients b and c
    use (f 1 - f (-1)) / 2, ((f 1 + f (-1)) / 2 - 1)
    intro x
    -- Apply the functional equation with specific values
    have h1:= h x 1
    have h2:= h (x + 1) (-1)
    simp at h1 h2
    -- Manipulate the equations to isolate f(x)
    have h3 : (x * f x - f 1) * (x + 1) = (x - 1) * (f (x + 1) - x) * (x + 1):= by rw [h1]
    have h4 : ((x + 1) * f (x + 1) + f (-1)) * (x - 1) = ((x + 1 + 1) * (f x - (-1 + -x))) * (x - 1):= by rw [h2]
    -- Combine the equations
    have h5 : (x * f x - f 1) * (x + 1) + f (-1) * (x - 1) = (x + 1 + 1) * (f x - (-1 + -x)) * (x - 1) - x * (x + 1) * (x - 1):= by linarith
    apply sub_eq_zero.2 at h5
    ring_nf at h5
    -- Solve for f(x) in terms of f(1) and f(-1)
    replace h5 : f x = -(2 - x * f 1 + (x * f (-1) - x ^ 2 * 2) + (-f 1 - f (-1))) / 2:= by linarith
    rw [h5]
    ring_nf
  -- Reverse direction: if f is a quadratic function, then it satisfies the functional equation
  .
    intro h
    rcases h with ⟨b, c, h⟩
    simp [h]
    intro x y
    linarith
