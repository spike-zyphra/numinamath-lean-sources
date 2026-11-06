import Mathlib

/-
Find all values of the parameter $a$ for which the roots $x_{1}$ and $x_{2}$ of the equation

$$
2 x^{2}-2016(x-2016+a)-1=a^{2}
$$

satisfy the double inequality $x_{1} < a < x_{2}$.
-/
theorem algebra_183226 {a : ℝ} (ha : ∃ x1 x2, x1 ≠ x2 ∧ 2*x1^2-2016*(x1-2016+a)-1=a^2 ∧ 2*x2^2-2016*(x2-2016+a)-1=a^2 ∧ x1<a ∧ a<x2) :
    2015 < a ∧ a < 2017 := by
  rcases ha with ⟨x1, x2, hx12, h1, h2, h3, h4⟩
  have eq_subtract : 2 * x1^2 - 2016 * (x1 - 2016 + a) - 1 - (2 * x2^2 - 2016 * (x2 - 2016 + a) - 1) = 0 := by linarith
  have h5 : (x1 - x2) * (2 * (x1 + x2) - 2016) = 0 := by
    ring_nf at eq_subtract ⊢
    nlinarith
  have h6 : 2 * (x1 + x2) - 2016 = 0 := by
    apply_fun (λ y => y / (x1 - x2)) at h5
    field_simp [sub_ne_zero.mpr hx12] at h5
    linarith
  have h7 : x1 + x2 = 1008 := by linarith
  have h8 : (a - 2016) ^ 2 < 1 := by
    nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 - a), sq_nonneg (x2 - a), h7]
  constructor
  · nlinarith
  · nlinarith
