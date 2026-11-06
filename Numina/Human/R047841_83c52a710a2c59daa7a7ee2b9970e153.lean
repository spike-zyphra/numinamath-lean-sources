import Mathlib
open Set

/- The function $f(x) = x^3 - 3ax + b$ ($a > 0$) has a maximum value of 6 and a minimum value of 2. Find the interval where $f(x)$ is monotonically decreasing. -/
theorem algebra_9288 (a b : ℝ) (ha : a > 0) (f : ℝ → ℝ)
    (hf : f = fun x => x ^ 3 - 3 * a * x + b)
    (x₁ : ℝ) (hx₁ : f x₁ = 6) (hmax : IsLocalMax f x₁) (x₂ : ℝ) (hx₂ : f x₂ = 2) (hmin : IsLocalMin f x₂) : AntitoneOn f (Icc (-1) 1) ∧ MonotoneOn f (Iic (-1)) ∧ MonotoneOn f (Ici 1) := by

  -- Calculate the derivative of f
  have hfder (x : ℝ) : deriv f x = 3 * x ^ 2 - 3 * a := by
    rw [hf]
    -- Use equality of derivatives
    rw [deriv_add, deriv_sub, deriv_pow, deriv_const_mul] <;> try simp
    -- Some differentiable conditions
    all_goals exact DifferentiableAt.const_mul differentiableAt_id (3 * a)

  -- Apply Fermat's theorem:
  -- If x is a local maximum or minimum of f, then f'(x) = 0
  apply IsLocalMax.deriv_eq_zero at hmax
  apply IsLocalMin.deriv_eq_zero at hmin

  -- Simplify the expressions
  rw [hfder, ←mul_sub] at hmax hmin
  simp at hmax hmin
  rw [sub_eq_zero] at hmax hmin

  -- x₁^2 = x₂^2, so x₁ = x₂ or x₁ = -x₂
  have h : x₁ = x₂ ∨ x₁ = -x₂ := sq_eq_sq_iff_eq_or_eq_neg.1 (by linarith)

  -- Clearly x₁ ≠ x₂, so x₁ = -x₂
  obtain h | h := h
  {
    rw [h] at hx₁
    linarith
  }

  -- Substitute x₁ = -x₂
  subst x₁
  -- Simplify the equations
  rw [hf] at hx₁ hx₂
  simp [Odd.neg_pow (by decide : Odd 3)] at hx₁ hx₂
  rw [←hmin, mul_assoc, ←pow_succ] at hx₁ hx₂
  simp at hx₁ hx₂

  -- We get x₂^3 = 1 and b = 4 from hx₁ and hx₂
  have h1 : x₂^3 = 1^3 := by linarith
  have hb : b = 4 := by linarith

  -- x₂ = 1 and thus a = 1
  rw [pow_eq_pow_iff_of_ne_zero (by norm_num)] at h1
  simp [(by decide : ¬Even 3)] at h1
  replace ha : a = 1 := by
    rw [h1] at hmin
    linarith

  -- Clear all hypotheses and simplify the goal
  clear hx₁ hx₂ h1 hmin hmax hfder x₂
  subst a b f
  simp

  -- We need to prove that f is monotonically decreasing on [-1, 1] and monotonically increasing on (-∞, -1] and [1, ∞)
  -- First introduce x, y, and the conditions
  refine ⟨?_ ,?_ ,?_⟩ <;>
  intro x hx y hy hxy <;>
  simp at * <;>

  -- LHS - RHS = x^3 - 3 * x + 3 * y - y^3 = (x - y) * (x^2 + x * y + y^2 - 3)
  have h1 : x^3 - 3 * x + 3 * y - y^3 = (x - y) * (x^2 + x * y + y^2 - 3) := by ring

  . -- When x ≤ y ∈ [-1, 1]
    -- x^2 ≤ 1, y^2 ≤ 1, x * y ≤ 1
    have h2 : x^2 ≤ 1 := by nlinarith
    have h3 : y^2 ≤ 1 := by nlinarith
    have h4 : x * y ≤ 1 := by nlinarith
    nlinarith

  all_goals
    -- When x ≤ y ∈ (-∞, -1]
    -- Or x ≤ y ∈ [1, ∞)
    -- x^2 ≥ 1, y^2 ≥ 1, x * y ≥ 1
    have h2 : x^2 ≥ 1 := by nlinarith
    have h3 : y^2 ≥ 1 := by nlinarith
    have h4 : x * y ≥ 1 := by nlinarith
    nlinarith
