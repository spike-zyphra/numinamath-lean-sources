import Mathlib

/- Example 7 Given a constant $a>0$, such that the function $f(x)$ for any real number $x$ satisfies $f(x)+f(x+a)+$ $f(x) f(x+a)=1$. Is $f(x)$ a periodic function? -/

theorem algebra_145949 (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
    (h : ∀ x, f x + f (x + a) + f x * f (x + a) = 1) :
    ∃ c > 0, Function.Periodic f c := by
  -- We will show that f is periodic with period 2a.
  use 2 * a
  -- It is positive by assumption.
  refine ⟨by positivity, ?_⟩
  -- Now we prove that, for any x, f(x+2a) = f(x).
  intro x
  -- By subtracting the hypothesis at x and x + a, we get the following equation.
  have : (f (x + 2 * a) - f x) * (1 + f (x + a)) = 0 := by
    rw [(by ring : (0 : ℝ) = 1 - 1)]
    nth_rw 2 [← h (x + a), ← h x]
    ring_nf
  -- The product is zero, so at least one of the factors is zero.
  rcases mul_eq_zero.mp this with (h1 | h2)
  · -- If the first factor is zero, we are done.
    exact sub_eq_zero.mp h1
  · -- If the second factor is zero, by substituting into the hypothesis, we get 1 = -1, a contradiction.
    rw [add_comm, add_eq_zero_iff_eq_neg] at h2
    have := h x
    rw [h2] at this
    ring_nf at this
    norm_num at this