import Mathlib

/- Given the function $y = 4^x - 6 \times 2^x + 8$, find the minimum value of the function and the value of $x$ at which this minimum is attained.-/
theorem algebra_9157 {f : ℝ → ℝ} (hf : ∀ x, f x = 4^x - 6 * 2^x + 8) :
    (∀ x, -1 ≤ f x) ∧ f (Real.logb 2 3) = -1 := by
  -- Let us consider the function $y = 4^x - 6 \cdot 2^x + 8$.
  -- We notice that $4^x$ can be written as  $(2^2)^x$ which is the same as $(2^x)^2$.
  -- Therefore, we can rewrite the function as
  -- $$y = (2^x)^2 - 6 \cdot 2^x + 8.$$
  have four_pow_eq_sq_two_pow (x : ℝ) : (4 : ℝ) ^ x = (2 ^ x) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
    norm_num
  constructor
  . intro x
    rw [hf, four_pow_eq_sq_two_pow]
    -- Now, let's set $t = 2^x$ where $t > 0$.
    -- Substituting $t$ into the equation gives us a new function:
    -- $$y = t^2 - 6t + 8, \quad t > 0.$$
    set t := (2 : ℝ) ^ x
    -- This is a quadratic function in $t$, and its graph is a parabola opening upward.
    -- The vertex of this parabola gives the minimum value of the function.
    -- The vertex form of a quadratic function $y = a(t - h)^2 + k$ is at the point $(h, k)$
    -- where $h$ is the value of $t$ that minimizes the function.
    -- Comparing this with our function, we have $a = 1$, and
    -- the vertex can be found using the formula $t = -\frac{b}{2a}$.
    -- Here, $a = 1$ and $b = -6$ so the vertex, or the point where the minimum value occurs,
    -- is at $t = -\frac{-6}{2 \cdot 1} = 3$.
    -- Thus, the minimum value of $y$ is obtained by
    -- substituting $t = 3$ into $y = t^2 - 6t + 8$, which yields:
    -- $$y_{\text{min}} = 3^2 - 6 \cdot 3 + 8 = 9 - 18 + 8 = -1.$$
    suffices 0 ≤ t ^ 2 - 6 * t + 9 by linarith
    rw [show t ^ 2 - 6 * t + 9 = (t - 3) ^ 2 by ring]
    positivity
  -- Since we set $t = 2^x$, we have $2^x = 3$. To find the value of $x$, we solve for $x$ using logarithms:
  -- $$x = \log_2{3}.$$
  rw [hf, four_pow_eq_sq_two_pow, Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
  -- Hence, the function reaches its minimum value of $\boxed{-1}$ when $x = \boxed{\log_2{3}}$.
  norm_num
