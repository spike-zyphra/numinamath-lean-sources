import Mathlib

/- If $x$ and $y$ are real numbers with $(x+y)^{4}=x-y$, what is the maximum possible value of $y$ ?-/
theorem algebra_611208 : IsGreatest {y : ℝ | ∃ x : ℝ, (x + y) ^ 4 = x - y} (3 * 2 ^ (1 / 3 : ℝ) / 16) := by
  -- Simplify the goal into two parts.
  simp [IsGreatest, upperBounds, -one_div]
  refine ⟨?_, ?_⟩
  . -- First show that such value of y is attainable, i.e., there is corresponding x such that (x + y)⁴ = x - y holds.
    -- Use x = 5 * 2 ^ (1 / 3) / 16.
    use 5 * 2 ^ (1 / 3 : ℝ) / 16
    ring_nf
    rw [<-Real.rpow_natCast, <-Real.rpow_mul (by norm_num), show (1 / 3 * (4 : ℕ) : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add (by norm_num)]
    ring
  . -- Now we show that under the condition (x + y)⁴ = x - y, the maximum value of y is 3 * 2 ^ (1 / 3) / 16.
    intro y x hxy
    -- Let u = x + y.
    let u := x + y
    -- Change the equation to u⁴ = u - 2y.
    rw [show x + y = u by rfl, show x - y = u - 2 * y by ring] at hxy
    -- Let f(u) = (u - u⁴) / 2.
    let f : ℝ → ℝ := fun u => (u - u ^ 4) / 2
    -- Change the equation to y = f(u).
    replace hxy : y = f u := by
      field_simp [f]
      linarith only [hxy]
    -- It suffices to show that f(u) ≤ 3 * 2 ^ (1 / 3) / 16.
    rw [hxy]
    -- Calculate the derivative f'(u) = 1 - 4u³.
    have hfder : deriv f = fun u => (1 - 4 * u ^ 3) / 2 := by
      ext u
      simp [f]
    -- Let x₀ = 2 ^ (1 / 3) / 2.
    let x₀ : ℝ := 2 ^ (1 / 3 : ℝ) / 2
    -- Show that f'(x₀) = 0.
    have h₀ : deriv f x₀ = 0 := by
      -- Substitute x₀ into the derivative.
      rw [hfder]
      -- Simplify the expression.
      field_simp [x₀]
      nth_rw 2 [<-Real.rpow_natCast]
      rw [<-Real.rpow_mul (by norm_num)]
      norm_num
    -- Show that f(x₀) is a local maximum of f.
    have h₁ : IsLocalMax f x₀ := by
      -- Use the theorem for determining the extrema of a function.
      apply isLocalMax_of_deriv
      . -- Verify that f is continuous at x₀.
        simp [f]
        -- It suffices to show that f is continuous at all x ∈ ℝ.
        apply Continuous.continuousAt
        continuity
      . -- Verify that f is eventually differentiable for x ∈ ℝ \ {x₀} near x₀.
        -- It suffices to show that f is differentiable at all x ∈ ℝ.
        suffices ∀ x : ℝ, DifferentiableAt ℝ f x by
          simp [this]
        intro x
        apply @Differentiable.differentiableAt
        aesop
      . -- Verify that f'(x₀) ≥ 0 eventually for x → x₀ on the left.
        -- It suffices to show that f'(x) ≥ 0 for all x < x₀.
        apply eventually_nhdsWithin_of_forall
        intro x
        simp [hfder]
        intro hx
        simp [hfder] at h₀
        -- Basically this is because x³ < x₀³ for all x < x₀.
        linarith [show x ^ 3 < x₀ ^ 3 by apply Odd.strictMono_pow (by use 1; rfl) hx]
      . -- Verify that f'(x₀) ≤ 0 eventually for x → x₀ on the right.
        -- It suffices to show that f'(x) ≤ 0 for all x > x₀.
        apply eventually_nhdsWithin_of_forall
        intro x
        simp [hfder]
        intro hx
        simp [hfder] at h₀
        -- Basically this is because x₀³ < x³ for all x > x₀.
        linarith [show x₀ ^ 3 < x ^ 3 by apply Odd.strictMono_pow (by use 1; rfl) hx]
    -- Show that f is concave.
    have h₂ : ConcaveOn ℝ Set.univ f := by
      apply concaveOn_univ_of_deriv2_nonpos
      . -- Show that f is differentiable.
        aesop
      . -- Show that f' is differentiable.
        simp [hfder]
        apply Differentiable.div_const
        aesop
      . -- Show that f''(x) = -6x² ≤ 0 for all x ∈ ℝ.
        intro x
        simp [hfder]
        field_simp
        rw [div_le_iff₀ (by norm_num)]
        simp
        positivity
    -- Show that f(x₀) is global maximum.
    replace h₁ := IsMaxOn.of_isLocalMax_of_convex_univ h₁ h₂
    -- The desired inequality is then clear.
    convert h₁ u using 1
    -- We only need to show that f(x₀) = 3 * 2 ^ (1 / 3) / 16 by some simplification and simple ring algebra.
    field_simp [f, x₀]
    ring_nf
    rw [<-Real.rpow_natCast, <-Real.rpow_mul (by norm_num), show (1 / 3 * (4 : ℕ) : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add (by norm_num)]
    ring
