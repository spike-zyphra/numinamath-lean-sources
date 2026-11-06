import Mathlib

/- Let $f(x)=x^{2}+6 x+7$. Determine the smallest possible value of $f(f(f(f(x))))$ over all real numbers $x$.-/
theorem algebra_609336 (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + 6 * x + 7) :
    IsLeast {y | ∃ x, y = f (f (f (f x)))} 23 := by
  -- Break the goal into two parts.
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- First show that 23 is attainable.
    use -3
    repeat norm_num [hf]
  . -- Now show that 23 is a lower bound.
    -- Show that f(x) ≥ -2 for all x.
    have h₀ (x : ℝ): f x ≥ -2 := by
      -- This is basically proving that (x + 3)² ≥ 0.
      rw [hf]
      linarith only [sq_nonneg (x + 3)]
    -- Note that f is increasing on the interval [-3, ∞).
    have h₁ (x y : ℝ) : -3 ≤ x → x ≤ y → f x ≤ f y := by
      intro hx hy
      rw [hf, hf]
      nlinarith
    -- Show that f(f(x)) ≥ f(-2) = -1 for all x.
    have h₂ (x : ℝ) : f (f x) ≥ -1 := by
      calc
        f (f x) ≥ f (-2) := by
          apply h₁
          norm_num
          exact h₀ x
        _ = -1 := by
          rw [hf]
          norm_num
    -- Show that f(f(f(x))) ≥ f(-1) = 2 for all x.
    have h₃ (x : ℝ) : f (f (f x)) ≥ 2 := by
      calc
        f (f (f x)) ≥ f (-1) := by
          apply h₁
          norm_num
          exact h₂ x
        _ = 2 := by
          rw [hf]
          norm_num
    -- Show that f(f(f(f(x)))) ≥ 23 for all x.
    have h₄ (x : ℝ) : f (f (f (f x))) ≥ 23 := by
      calc
        f (f (f (f x))) ≥ f 2 := by
          apply h₁
          norm_num
          exact h₃ x
        _ = 23 := by
          rw [hf]
          norm_num
    exact h₄
