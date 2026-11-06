import Mathlib

/- Determine all real-valued functions $f(x)$ in one variable such that the relation $f([f(x)]^2 + f(y)) = xf(x) + y$ holds for all real numbers $x$ and $y$. -/
theorem algebra_615323 :
    {f : ℝ → ℝ | ∀ x y, f (f x ^ 2 + f y) = x * f x + y} = {(·), (-·)} := by
  ext f
  simp
  constructor
  -- We first verify that x => x and x => -x are solutions.
  swap
  . rintro (rfl | rfl)
    all_goals
      intro x y
      simp
      ring
  . intro H
    -- Setting y = 0, we get f (f 0 ^ 2 + f y) = y
    have H₁ y := H 0 y
    simp at H₁
    -- So f is both injective and surjective.
    have H₂ : f.Injective := by
      intro x y h
      rw [← H₁ x, ← H₁ y, h]
    have H₃ : f.Surjective := by
      intro y
      exact ⟨f 0 ^ 2 + f y, H₁ y⟩
    -- There exists some t such that f t = 0.
    obtain ⟨t, ht⟩ : ∃ t, f t = 0 := H₃ 0
    -- For all y, we have f (f y) = y.
    have H₄ (y : ℝ) : f (f y) = y := by
      simpa [ht] using H t y
    -- We have f 0 = 0.
    -- Since f (f 0 ^ 2 + f 0) = 0 = f (f 0), so f 0 ^ 2 = 0.
    have H₅ : f 0 = 0 := by
      specialize H₁ 0
      conv_rhs at H₁ =>
        rw [← H₄ 0]
      simpa using H₂ H₁
    -- Set y = 0 in the original equation, we get f (f x ^ 2) = x * f x.
    have H₆ x : f (f x ^ 2) = x * f x := by
      simpa [H₅] using H x 0
    -- Let's calculate f (x ^ 2).
    have H₇ x : f (x ^ 2) = x * f x := by
      calc f (x ^ 2)
        _ = f (f (f x) ^ 2) := by rw [H₄ x]
        _ = f x * f (f x) := by rw [H₆]
        _ = f x * x := by rw [H₄ x]
        _ = x * f x := by ring
    -- So f x ^ 2 = x ^ 2.
    have H₈ x := H₂ ((H₆ x).trans (H₇ x).symm)
    -- That is f x = x ∨ f x = -x.
    simp [sq_eq_sq_iff_eq_or_eq_neg] at H₈
    -- If there is some a, b such that f a = a, f b = -b, a ≠ 0, b ≠ 0, then we can derive a contradiction.
    have H₉ (a b : ℝ) (ha₁ : a ≠ 0) (hb₁ : b ≠ 0) (ha₂ : f a = a) (hb₂ : f b = -b) : False := by
      -- Take x = a, y = b in the original equation, we get f (a ^ 2 + b) = a * a + b.
      have h₁ := H a b
      rw [ha₂, hb₂] at h₁
      -- But f (a ^ 2 + b) = ±(a ^ 2 + b), so we have a contradiction.
      obtain h₂ | h₂ := H₈ (a ^ 2 + -b)
      . absurd hb₁
        linarith
      . absurd ha₁
        apply pow_eq_zero (n := 2)
        linarith
    -- Let's proceed case analysis on f 1.
    rcases H₈ 1 with K | K
    . -- If f 1 = 1, then f x ≠ x is impossible.
      -- So f x = x for all x.
      left
      ext x
      by_cases hx : x = 0
      . simp [hx, H₅]
      specialize H₉ 1 x (by simp) hx K
      specialize H₈ x
      tauto
    . -- If f 1 = -1, then f x ≠ x is impossible.
      -- So f x = -x for all x.
      right
      ext x
      by_cases hx : x = 0
      . simp [hx, H₅]
      replace H₉ : ¬f x = x := fun h => H₉ x 1 hx (by simp) h K
      specialize H₈ x
      tauto
