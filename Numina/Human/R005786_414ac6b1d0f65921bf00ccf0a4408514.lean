import Mathlib

/- Over all real numbers $x$ and $y$, find the minimum possible value of

$$
(x y)^{2}+(x+7)^{2}+(2 y+7)^{2}
$$-/
theorem algebra_609919 :
    IsLeast {z | ∃ x y : ℝ, z = (x * y) ^ 2 + (x + 7) ^ 2 + (2 * y + 7) ^ 2} 45 := by
  -- Show a lemma that the function f(y) = 49(1 - 1/(y^2+1))+(2y+7)^2 attains minimal value 45.
  let f : ℝ → ℝ := fun y => 49 * (1 - 1 / (y ^ 2 + 1)) + (2 * y + 7) ^ 2
  -- Show that f(y) = (2y^2 + 7y + 2)^2/(y^2+1) + 45.
  have hf₀ (y : ℝ) : f y = (2 * y ^ 2 + 7 * y + 2) ^ 2 / (y ^ 2 + 1) + 45 := by
    field_simp [f]
    ring
  -- Let y₀ := (Real.sqrt 33 - 7) / 4.
  let y₀ := (Real.sqrt 33 - 7) / 4
  -- We have f(y₀) = 45.
  have hy₀ : f y₀ = 45 := by
    rw [hf₀]
    simp
    -- We have 2y₀² + 7y₀ + 2 = 0.
    left
    field_simp [y₀, sub_sq]
    ring
  -- First simplify the goal into two parts.
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- First show that the minimum value 45 is possible.
    -- Let x₀ = -7/(y₀²+1).
    let x₀ := -7 / (y₀ ^ 2 + 1)
    -- Substitute x₀ and y₀ into the expression.
    use x₀, y₀
    simp [x₀]
    rw [<-hy₀, hf₀ y₀]
    clear_value y₀
    field_simp
    ring
  . -- Show that the 45 is the least possible value.
    -- Fix y and let x vary.
    intro z x y hz
    rw [hz]
    clear z hz
    revert x
    -- Let g(x) = (xy)² + (x + 7)² + (2y + 7)², and we view it as function of x.
    let g : ℝ → ℝ := fun x => y ^ 2 * x ^ 2 + x ^ 2 + 14 * x + 49 + (2 * y + 7) ^ 2
    -- Calculate the derivative g'(x) = 2xy² + 2(x + 7).
    have hgder : deriv g = fun x => 2 * (x * (y ^ 2 + 1) + 7) := by
      ext x
      simp [g]
      -- Use equality of derivatives.
      rw [deriv_add, deriv_add, deriv_const_mul, deriv_const_mul, deriv_pow, deriv_id'']
      <;> try simp
      ring
      -- Verify some differentiable conditions that is not tackled by simp.
      exact DifferentiableAt.const_mul differentiableAt_id 14
    -- Let x₀ = -7/(y²+1).
    let x₀ := -7 / (y ^ 2 + 1)
    -- Show that g'(x₀) = 0.
    have h₀ : deriv g x₀ = 0 := by
      -- Substitute x₀ into the derivative.
      rw [hgder]
      -- Simplify the expression.
      field_simp [x₀]
    -- Show that x₀ is the minimum of g.
    have h₁ : IsLocalMin g x₀ := by
      -- Use the theorem for determining the extrema of a function.
      apply isLocalMin_of_deriv
      . -- Verify that g is continuous at x₀.
        simp [g]
        repeat apply ContinuousAt.add
        . apply ContinuousAt.mul
          apply continuousAt_const
          apply continuousAt_pow
        . apply continuousAt_pow
        . apply ContinuousAt.mul
          apply continuousAt_const
          apply continuousAt_id
        . apply continuousAt_const
        . apply continuousAt_const
      . -- Verify that g is eventually differentiable for x ∈ ℝ \ {x₀} near x₀.
        -- It suffices to show that g is differentiable at all x ∈ ℝ.
        suffices ∀ x : ℝ, DifferentiableAt ℝ g x by
          simp [this]
        intro x
        simp [g]
        repeat apply DifferentiableAt.add
        . apply DifferentiableAt.mul
          apply differentiableAt_const
          apply differentiableAt_pow
        . apply differentiableAt_pow
        . apply DifferentiableAt.mul
          apply differentiableAt_const
          apply differentiableAt_id
      . -- Verify that g'(x₀) ≤ 0 eventually for x → x₀ on the left.
        -- It suffices to show that g'(x) ≤ 0 for all x < x₀.
        apply eventually_nhdsWithin_of_forall
        intro x
        simp [hgder]
        intro hx
        simp [hgder] at h₀
        nlinarith [show 0 < y ^ 2 + 1 by positivity]
      . -- Verify that g'(x₀) ≥ 0 eventually for x → x₀ on the right.
        -- It suffices to show that g'(x) ≥ 0 for all x > x₀.
        apply eventually_nhdsWithin_of_forall
        intro x
        simp [hgder]
        intro hx
        simp [hgder] at h₀
        nlinarith [show 0 < y ^ 2 + 1 by positivity]
    -- Show that g is convex.
    have h₂ : ConvexOn ℝ Set.univ g := by
      apply convexOn_univ_of_deriv2_nonneg
      . -- Show that g is differentiable.
        simp [g]
        repeat apply Differentiable.add
        . apply Differentiable.mul
          apply differentiable_const
          apply differentiable_pow
        . apply differentiable_pow
        . apply Differentiable.mul
          apply differentiable_const
          apply differentiable_id
      . -- Show that g' is differentiable.
        rw [hgder]
        apply Differentiable.const_mul
        apply Differentiable.add_const
        apply Differentiable.mul_const
        apply differentiable_id
      . -- Show that g''(x) = 2(y² + 1) > 0.
        intro x
        simp [hgder]
        positivity
    -- Show that g(x₀) is global minimum.
    replace h₁ := IsMinOn.of_isLocalMin_of_convex_univ h₁ h₂
    -- Now we proceed wit the original inequality and let x vary.
    intro x
    calc
      _ = g x := by
        -- The left hand side is g(x) we defined.
        simp [g]
        ring
      _ ≥ g x₀ := by
        -- Use the minimality of g(x₀).
        exact h₁ x
      _ = f y := by
        -- Substitute x₀ into the expression to get g(x₀) = f(y).
        simp [hf₀, g, x₀]
        -- Simplify the expression.
        field_simp [x₀]
        ring
      _ ≥ 45 := by
        -- Use the alternate form of f(y) we have proved earlier.
        rw [hf₀]
        simp
        positivity
