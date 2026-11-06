import Mathlib

/- Find all functions $f$ such that

$$
f(f(x)+y)=f\left(x^{2}-y\right)+4 y f(x)
$$

for all real numbers $x$ and $y$. -/
theorem inequalities_608012 :
  {f : ℝ → ℝ | ∀ x y : ℝ, f (f x + y) = f (x ^ 2 - y) + 4 * y * f x} = {0, (· ^ 2)} := by
  ext f
  simp
  constructor
  -- First, we verify that f = 0 and f(x) = x ^ 2 are solutions.
  swap
  . rintro (rfl | rfl)
    . simp
    . simp
      intro x y
      ring
  -- Next, we show that any solution must be one of the above.
  . intro H
    -- Substituting y = x ^ 2, we get f(f(x) + x ^ 2) = f(0) + 4 * x ^ 2 * f(x).
    -- Substituting y = -f(x), we get f(0) = f(x ^ 2 + f(x)) - 4 * f(x) ^ 2.
    -- Adding these two equations, we get f(x) = 0 or f(x) = x ^ 2.
    have h₁ (x : ℝ) : f x = 0 ∨ f x = x ^ 2 := by
      have h₁ := H x (x ^ 2)
      have h₂ := H x (-f x)
      simp at h₁ h₂
      ring_nf at h₁ h₂
      have h₃ : f x * (f x - x ^ 2) = 0 := by linear_combination (h₁ + h₂) / 4
      simp [sub_eq_zero] at h₃
      exact h₃
    -- We rewrite the given equation in a more convenient form.
    -- The proof is tautological.
    have h₁' {x : ℝ} : f x ≠ 0 → f x = x ^ 2 := by
      intro h
      specialize h₁ x
      simp [h] at h₁
      exact h₁
    -- Specializing to x = 0, we get f(0) = 0.
    have h₂ : f 0 = 0 := by
      specialize h₁ 0
      simp at h₁
      exact h₁
    -- Case analysis on whether f(x) = 0 for all non-zero x.
    by_cases h₃ : ∃ a ≠ 0, f a ≠ 0
    . -- If there exists some a ≠ 0 such that f(a) ≠ 0, then f(a) = a ^ 2.
      rcases h₃ with ⟨a, ha, hfa⟩
      have h₄ : f a = a ^ 2 := by
        specialize h₁ a
        simp [hfa] at h₁
        exact h₁
      -- Substituting x = a, we get f(a ^ 2 + y) = f(a ^ 2 - y) + 4 * y * f(a).
      have h₅ := H a
      simp [h₄] at h₅
      -- We now prove that for any x ≠ 0, f(x) ≠ 0.
      have h₆ {x} (hx : x ≠ 0) : f x ≠ 0 := by
        -- Set y := a ^ 2 - x.
        let y := a ^ 2 - x
        -- WLOG, assume y ≠ 0.
        wlog yne0 : y ≠ 0 generalizing x with K
        {
          -- If y = 0, then x = a ^ 2
          -- We already know that f(-a ^ 2) ≠ 0 by the hypothesis.
          -- And substituting x = 0 and y = a ^ 2 in the original equation, we get
          -- f(a ^ 2) = f(-a ^ 2)
          -- So we get the desired result that f(x) ≠ 0.
          simp [y, sub_ne_zero] at yne0
          subst yne0
          specialize K (show -a ^ 2 ≠ 0 from neg_ne_zero.mpr (pow_ne_zero 2 ha))
          simp [ha] at K
          specialize H 0 (a ^ 2)
          simp [h₂] at H
          rwa [H]
        }
        -- x = a ^ 2 - y
        have hy : x = a ^ 2 - y := by simp [y]
        -- Supose f(x) = 0.
        contrapose! hx
        -- Then f(a ^ 2 - y) = 0, and f(a ^ 2 + y) = 4 * y * a ^ 2 ≠ 0.
        specialize h₅ y
        simp [← hy, hx] at h₅
        have h₆ : 4 * y * a ^ 2 ≠ 0 := by positivity
        rw [← h₅] at h₆
        -- So (a ^ 2 + y) ^ 2 = 4 * y * a ^ 2.
        -- We obtain a ^ 2 - y = 0 from this identity.
        -- That is, x = 0.
        specialize h₁' h₆
        rw [h₅] at h₁'
        replace h₁' : (a ^ 2 - y) ^ 2 = 0 := by linear_combination -h₁'
        simp at h₁'
        rwa [hy]
      -- Now any non-zero x satisfies f(x) ≠ 0, and thus f(x) = x ^ 2.
      right
      ext x
      by_cases hx : x = 0
      . subst hx
        simpa
      . exact h₁' (h₆ hx)
    . -- If f(x) = 0 for all non-zero x, then f is the zero function.
      simp at h₃
      left
      ext x
      by_cases hx : x = 0
      . subst hx
        simpa
      . exact h₃ x hx
