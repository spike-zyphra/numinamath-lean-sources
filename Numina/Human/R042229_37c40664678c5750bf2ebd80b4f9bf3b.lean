import Mathlib

/-Let $x_1,$ $x_2,$ $\dots,$ $x_{100}$ be real numbers such that $x_1 + x_2 + \dots + x_{100} = 1$ and
\[\frac{x_1}{1 - x_1} + \frac{x_2}{1 - x_2} + \dots + \frac{x_{100}}{1 - x_{100}} = 1.\]Find
\[\frac{x_1^2}{1 - x_1} + \frac{x_2^2}{1 - x_2} + \dots + \frac{x_{100}^2}{1 - x_{100}}.\]-/
theorem algebra_13849 (x : Fin 100 → ℝ) (hsum : ∑ i, x i = 1) (h_ne_one: ∀ i, x i ≠ 1)
    (hfraction : ∑ i, x i / (1 - x i) = 1) :
    ∑ i, (x i) ^ 2 / (1 - x i) = 0 := by
  -- In general, \[\frac{x^2}{1 - x} = \frac{x^2 - x + x}{1 - x} = \frac{x(x - 1) + x}{1 - x} = \frac{x}{1 - x} - x,\]
  have eq: ∀(x : ℝ), x ≠ 1 → (x ^ 2 / (1 - x) = x / (1 - x) - x) := by
    intro x hx
    have : x^2 = x - x * (1 - x) := by linarith
    rw [this, sub_div, ←mul_div, div_self (sub_ne_zero_of_ne (Ne.symm hx)), mul_one]
  -- so \frac{x_1^2}{1 - x_1} + \frac{x_2^2}{1 - x_2} + \dots + \frac{x_{100}^2}{1 - x_{100}} &= \frac{x_1}{1 - x_1} + \frac{x_2}{1 - x_2} + \dots + \frac{x_{100}}{1 - x_{100}} - (x_1 + x_2 + \dots + x_{100})
  have : (fun i ↦ x i ^ 2 / (1 - x i)) = (fun i ↦ x i / (1 - x i) - x i) := by
    ext i
    rw [eq _ (h_ne_one i)]
  -- &= 1 - 1 = 0
  rw [Finset.sum, this, ←Finset.sum, Finset.sum_sub_distrib, hfraction, hsum, sub_self]
