import Mathlib
open Real Set
open scoped BigOperators

/-
$f$ is a function defined on $(1,+\infty)$ and takes values in $(1,+\infty)$, satisfying the condition: for any $x, y>1$ and $u, v>0$, it holds that
$$
f\left(x^{u} y^{u}\right) \leqslant f(x)^{\frac{1}{4 u} f(y)^{\frac{1}{40}}}
$$

Determine all such functions $f$.
-/
theorem inequalities_283376 {f : ℝ → ℝ}
  (hf : ∀ x > 1, f x > 1)
  (h : ∀ x y : ℝ, x > 1 → y > 1 →
    ∀ u v : ℝ, u > 0 → v > 0 →
      f (x^u * y^u) ≤ (f x)^(1 / (4 * u)) * (f y)^(1 / (40 * u))) :
  ∀ x > 1, f x = x^(1 / log x) := by 
  intro x hx

  /-
  First, we take u = 1/2 and y = x in the original inequality:
  f(x^(1/2) * x^(1/2)) ≤ (f(x))^(1/(4*(1/2))) * (f(x))^(1/(40*(1/2)))
  -/
  have h1 := h x x hx hx (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have h2 : f (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) ≤ (f x)^(1 / (4 * (1 / 2 : ℝ))) * (f x)^(1 / (40 * (1 / 2 : ℝ))) := by 
    simpa using h1

  /- 
  The left side can be simplified:
    x^(1/2) * x^(1/2) = x^(1/2 + 1/2) = x^1 = x
  Therefore f(x^(1/2) * x^(1/2)) = f(x)
  -/
  have h3 : f (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) = f x := by 
    have h4 : (x : ℝ) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by 
      have h5 : (x : ℝ) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by 
        rw [Real.rpow_add]
        all_goals linarith
      rw [h5]
      norm_num
    rw [h4]
  rw [h3] at h2

  /-
  The right side can be simplified:
    (f(x))^(1/(4*(1/2))) * (f(x))^(1/(40*(1/2)))
    = (f(x))^(1/2) * (f(x))^(1/20)
    = (f(x))^(11/20)
  -/
  have h6 : (f x) ^ (1 / (4 * (1 / 2 : ℝ))) * (f x) ^ (1 / (40 * (1 / 2 : ℝ))) = (f x) ^ (11 / 20 : ℝ) := by 
    rw [← Real.rpow_add]
    field_simp
    ring_nf
    all_goals linarith [hf x hx]
  rw [h6] at h2

  /-
  So the inequality becomes f(x) ≤ (f(x))^(11/20)
  However, since f(x) > 1 (given condition) and 11/20 < 1,
  by the properties of exponential functions:
  when the base is greater than 1, smaller exponent means smaller power
  Therefore (f(x))^(11/20) < f(x).
  -/
  have h7 : (f x) > 1 := hf x hx
  have h8 : (f x) ^ (11 / 20 : ℝ) < (f x) := by 
    have h9 : (f x) > 1 := h7
    have h10 : (f x) ^ (11 / 20 : ℝ) < (f x) ^ (1 : ℝ) := by 
      apply Real.rpow_lt_rpow_of_exponent_lt
      · linarith
      · norm_num
    rw [show (f x : ℝ) ^ (1 : ℝ) = f x by simp] at h10
    linarith

  -- Hence, we conclude f(x) = (f(x))^(1/40) by capping both ends.
  linarith [h8, h2]