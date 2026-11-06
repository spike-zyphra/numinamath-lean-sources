import Mathlib

/- . Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that

$$
f(x+y)+y \leqslant f(f(f(x)))
$$

holds for all $x, y \in \mathbb{R}$. -/
theorem algebra_606203 :
    {f : ℝ → ℝ | ∀ x y, f (x + y) + y ≤ f (f (f x))} = {f : ℝ → ℝ| ∃ c, ∀ z, f z = c - z} := by
  -- Break the goal into two parts.
  ext f
  apply Iff.intro
  . -- First show that the condition would imply that f(z) = c - z.
    simp
    intro h₀
    -- Write z = x + y.
    have h₁ (x z : ℝ) : f z + z ≤ f (f (f x)) + x := by
      specialize h₀ x (z - x)
      simp at h₀
      linarith
    -- Show that f(f(x)) ≤ x.
    have h₂ (x : ℝ) : f (f x) ≤ x := by
      -- Substitute z = f(f(x)) into the previous inequality.
      specialize h₁ x (f (f x))
      simp_all
    -- We have f(z) + z ≤ f(x) + x for all x, z.
    have h₃ (x z : ℝ) : f z + z ≤ f x + x := by
      linarith only [h₂ (f x), h₁ x z]
    -- Show that f(z) = c - z for some c.
    have h₄ : ∃ c, ∀ z, f z = c - z := by
      -- Let c = f(0) + 0.
      use f 0 + 0
      intro z
      linarith only [h₃ z 0, h₃ 0 z]
    exact h₄
  . -- Next show that f(z) = c - z would satisfy the condition.
    simp
    intro c hf x y
    simp [hf]
    ring_nf
    rfl
