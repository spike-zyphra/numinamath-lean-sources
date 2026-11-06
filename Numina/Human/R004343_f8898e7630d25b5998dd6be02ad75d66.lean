import Mathlib

open Real Set
open scoped BigOperators

/- Example 9 Given the function $f(x)=x^{2}+a|x|+x, x \in \mathbf{R}, a \in \mathbf{R}$.
(1) If $x_{1}, x_{2} \in(0,+\infty)$, compare $\frac{1}{2}\left[f\left(x_{1}\right)+f\left(x_{2}\right)\right]$ with $f\left(\frac{x_{1}+x_{2}}{2}\right)$.
(2) If $x_{1}, x_{2} \in \mathbf{R}$, and $\frac{1}{2}\left[f\left(x_{1}\right)+f\left(x_{2}\right)\right]$ is compared with $f\left(\frac{x_{1}+x_{2}}{2}\right)$, and the result is consistent with (1), find the range of values for $a$. -/
theorem algebra_254990 {a : ℝ} (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 2 + a * abs x + x) :
    (∀ x₁ x₂ : ℝ, (f x₁ + f x₂) / 2 ≥ f ((x₁ + x₂) / 2)) ↔ a ≥ 0 := by
  constructor
  · -- Show that if the inequality holds, then a is nonnegative
    intro h
    -- Use contradiction
    by_contra!
    -- Let x₁ and x₂ be a / 2 and -(a / 2)
    specialize h (a / 2) (-(a / 2))
    rw [h₀, h₀, h₀] at h
    simp [abs_eq_neg_self.mpr (show 0 ≥ a / 2 by nlinarith), abs_eq_self.mpr (show 0 ≤ -a / 2 by linarith)] at h
    -- Simplify the expression
    suffices 1 / 2 * (- (a ^ 2 / 2)) < 0 by
      linarith
    nlinarith
  -- Show that if a is nonnegative and x₁ and x₂ are nonnegative, then the inequality holds
  intro ha x y
  rw [h₀, h₀, h₀]
  -- Casework by sign of x and y
  rcases lt_or_ge x 0 with hx | hx <;> rcases lt_or_ge y 0 with hy | hy
  · -- Both x and y are negative
    have mean_nonpos : (x + y) / 2 ≤ 0 := by linarith
    -- Since x, y, and (x + y) / 2 are negative, we can simplify their absolute values
    simp [abs_eq_neg_self.mpr mean_nonpos, abs_eq_neg_self.mpr (show x ≤ 0 by linarith), abs_eq_neg_self.mpr (show y ≤ 0 by linarith)]
    rw [div_pow, add_sq, pow_two 2, ← div_div]
    -- Simplify the expression to trivial inequality
    suffices (x - y) ^ 2 / 4 ≥ 0 by
      linarith
    nlinarith
  · -- x is negative and y is nonnegative
    -- Casework on the sign of the mean
    rcases lt_or_ge ((x + y) / 2) 0 with hm | hm
    · -- The mean is negative
      simp [abs_eq_neg_self.mpr (show (x + y) / 2 ≤ 0 by linarith), abs_eq_neg_self.mpr (show x ≤ 0 by linarith), abs_eq_self.mpr hy]
      -- Simplify the inequality
      suffices (x - y) ^ 2 / 4 + a * y ≥ 0 by
        linarith
      nlinarith
    -- The mean is nonnegative
    simp [abs_eq_self.mpr (show (x + y) / 2 ≥ 0 by linarith), abs_eq_neg_self.mpr (show x ≤ 0 by linarith), abs_eq_self.mpr hy]
    -- Simplify the inequality
    suffices (x - y) ^ 2 / 4 - a * x ≥ 0 by
      linarith
    nlinarith
  · -- y is negative and x is nonnegative
    -- Casework on the sign of the mean
    rcases lt_or_ge ((x + y) / 2) 0 with hm | hm
    · -- The mean is negative
      simp [abs_eq_neg_self.mpr (show (x + y) / 2 ≤ 0 by linarith), abs_eq_self.mpr (show x ≥ 0 by linarith), abs_eq_neg_self.mpr (show y ≤ 0 by linarith)]
      -- Simplify the inequality
      suffices (x - y) ^ 2 / 4 + a * x ≥ 0 by
        linarith
      nlinarith
    -- The mean is nonnegative
    simp [abs_eq_self.mpr (show (x + y) / 2 ≥ 0 by linarith), abs_eq_self.mpr (show x ≥ 0 by linarith), abs_eq_neg_self.mpr (show y ≤ 0 by linarith)]
    -- Simplify the inequality
    suffices (x - y) ^ 2 / 4 - a * y ≥ 0 by
      linarith
    nlinarith
  -- Both x and y are nonnegative
  -- Unfold definition of f
  -- The mean of x and y is nonnegative
  have mean_nonneg : 0 ≤ (x + y) / 2 := by linarith
  -- Since x, y, and (x + y) / 2 are positive, we can simplify their absolute values
  simp [abs_eq_self.mpr mean_nonneg, abs_eq_self.mpr (show 0 ≤ x by linarith), abs_eq_self.mpr (show 0 ≤ y by linarith)]
  rw [div_pow, add_sq, pow_two 2, ← div_div]
  -- Simplify the expression to trivial inequality
  suffices (x - y) ^ 2 / 4 ≥ 0 by
    linarith
  nlinarith