import Mathlib

open Real Set

theorem inequalities_597312 :
    IsLeast {c : ℝ | ∀ x y : ℝ, 1 + (x + y)^2 ≤ c * (1 + x^2) * (1 + y^2)} (4 / 3) := by
  constructor
  · -- Show that 4/3 is in the set
    intro x y
    have h : 1 + (x + y)^2 ≤ (4 / 3) * (1 + x^2) * (1 + y^2) := by
      nlinarith [sq_nonneg (x * y - 1 / 2), sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x * y - 1 / 2), sq_nonneg (x + 1 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (x * y), sq_nonneg (x ^ 2 * y ^ 2)]
    linarith
  · -- Show that 4/3 is the smallest
    intro c hc
    have h1 := hc (√2 / 2) (√2 / 2)
    -- Let's compute the left and right sides to find that equality holds when $c =4/3$.
    -- Left side is $1 + (√2/2 + √2/2)^2 = 3$
    -- Right side is $c*(1 + (√2/2)^2)^2 = 9/4*c$
    -- So $c \geq 4/3$.
    have h2 : 1 + (√2 / 2 + √2 / 2) ^ 2 = 3 := by
      have h3 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    have h3 : (√2 / 2 : ℝ) ^ 2 = 1 / 2 := by
      have h4 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith
    have h4 : (1 + (√2 / 2 : ℝ) ^ 2) * (1 + (√2 / 2 : ℝ) ^ 2) = (3 / 2 : ℝ) ^ 2 := by
      rw [h3]
      nlinarith
    -- Now the value of $c \geq 4/3$.
    nlinarith [Real.sqrt_nonneg 2]