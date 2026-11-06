import Mathlib

/- Let $a, b$, and $c$ be real numbers such that $a-7b+8c = 4$ and $8a+4b-c = 7$. Find $a^2 - b^2 + c^2.$-/
theorem algebra_19689 (a b c : ℝ) (h₀ : a - 7 * b + 8 * c = 4) (h₁ : 8 * a + 4 * b - c = 7) :
    a ^ 2 - b ^ 2 + c ^ 2 = 1 := by
  -- We have $a+8c = 4+7b$
  replace h₀ : a + 8 * c = 4 + 7 * b := by linear_combination h₀
  -- and $8a-c = 7-4b$.
  replace h₁ : 8 * a - c = 7 - 4 * b := by linear_combination h₁
  --Squaring both equations and adding the results yields $$
  --(a+8c)^2 + (8a-c)^2 = (4+7b)^2 + (7-4b)^2.
  have h : (a + 8 * c)^2 + (8 * a - c)^2= (4 + 7 * b)^2 + (7 - 4 * b)^2 := by
    apply_fun (· ^ 2) at h₀ h₁
    linear_combination h₀ + h₁
  -- $$Expanding gives $65(a^2+c^2) = 65(1+b^2)$.
  replace h : 65 * (a ^ 2 + c ^ 2) = 65 * (1 + b ^ 2) := by linear_combination h
  -- So $a^2 + c^2 = 1 + b^2$,
  rw [mul_right_inj' (by norm_num)] at h
  -- and $a^2-b^2+c^2 = \boxed{1}$.
  linear_combination h
