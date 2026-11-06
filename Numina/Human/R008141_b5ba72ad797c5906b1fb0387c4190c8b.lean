import Mathlib

open Real Set
open scoped BigOperators

/- Let \[f(x) = \left\{
\begin{array}{cl}
2x + 7 & \text{if } x < -2, \\
-x^2 - x + 1 & \text{if } x \ge -2.
\end{array}
\right.\]Find the sum of all values of $x$ such that $f(x) = -5.$ -/
theorem algebra_11063 {f : ℝ → ℝ}
  (hf : ∀ x, x < -2 → f x = 2 * x + 7)
  (hf' : ∀ x, x ≥ -2 → f x = -x ^ 2 - x + 1) :
  ∑ᶠ x ∈ {x | f x = -5}, x = -4 := by
  -- to find sum of all values satisfy f(x)=-5, we should solve f(x)=-5 first. and we claim it has two solutions: -6 and 2.
  have h1: {x | f x = -5} = {(-6:ℝ), (2:ℝ)} := by
    ext x
    simp
    constructor <;> intro h
    -- given f(x)=-5, find the solution. since x≥ -2 and x < -2 are different functions, we consider two cases.
    by_cases hx: x ≥ -2
    rw [hf' x hx] at h
    -- when x≥ -2, the equation is -x^2-x+1=-5, and it is x^2+x-6=0
    have h1: x^2+x-6 = 0 := by
      have: x^2+x-6 = x^2+x-1 + -5 := by ring
      rw [this, ← h]; ring
    -- factorization, x^2+x-6=(x+3)(x-2)
    have h2: (x+3)*(x-2) = 0 := by
      have: (x+3)*(x-2) = x^2+x-6 := by ring
      rw [this]; exact h1
    -- thus x+3=0 ∨ x-2=0, x=-3 or 2. and in this case x≥ -2, so x=2 is the only solution.
    have h3: x+3 = 0 ∨ x-2 = 0 := mul_eq_zero.mp h2
    rcases h3 with h31 | h32
    have: x = -3 := by
      rw [← add_zero (-3), ← h31]; ring
    rw [this] at hx; linarith [hx]
    right
    rw [← add_zero 2, ← h32]; ring
    push_neg at hx
    rw [hf x hx] at h
    -- when x < -2, the equation is 2x+7=-5. so 2x=-12
    have h1: 2*x = 2* (-6) := by
      have: 2*x = 2*x+7 - 7 := by ring
      rw [this, h]; ring
    -- obviously, 2x=-12, we have x=-6
    left
    have: x = 2*x /2 := by ring
    rw [this, h1]; ring
    -- the other direction. verify x=-6 and x=2 are two solutions.
    rcases h with h1 | h1
    have h2: -6 < (-2:ℝ) := by norm_num
    rw [h1, hf (-6) h2]; ring
    have h2: 2 ≥ (-2:ℝ) := by norm_num
    rw [h1, hf' 2 h2]; ring
  -- we have prove solution set of f(x)=-5 is {-6,2}. so sum of all values satisfying f(x)=-5 is just sum of set {-6,2}.
  rw [h1]
  -- -6+2=-4, so answer is -4.
  rw [finsum_mem_pair (by norm_num)]
  norm_num