import Mathlib

/- Trouver toutes les fonctions $f: \mathbb{R} \rightarrow \mathbb{R}$ telles que $f(f(x)+3 y)=12 x+f(f(y)-x)$ pour tous $x, y \in \mathbb{R}$. -/
theorem algebra_607624 (f : ℝ → ℝ) :
    (∀ x y, f (f x + 3 * y) = 12 * x + f (f y - x)) ↔ ∃ a, ∀ x, f x = a + 3 * x := by
  -- Split the iff into two implications.
  apply Iff.intro
  . -- First show that the functional equation implies the specific form.
    intro h₀
    -- Show that f is surjective.
    have h₁ : ∀ b, ∃ a, f a = b := by
      intro b
      -- Take y = -f(x) / 3 in h₀.
      replace h₀ (x : ℝ) : f 0 - 12 * x = f (f (-f x / 3) - x) := by
        specialize h₀ x (-f x / 3)
        rw [mul_div_cancel₀ _ (by norm_num), <-sub_eq_add_neg] at h₀
        simp_all
      -- So f 0 - 12x = f (f (-f x / 3) - x) for all x.
      -- Let a = f (-f x / 3) - x, b = f 0 - 12 x to show surjectivity.
      use f (-f ((f 0 - b) / 12) / 3) - ((f 0 - b) / 12)
      rw [<-h₀]
      linarith only []
    -- Show that f is injective.
    have h₂ (a b : ℝ) : f a = f b → a = b := by
      intro h
      -- Specialize y = a and y = b respectively in h₀.
      have h₀a (x : ℝ) := h₀ x a
      have h₀b (x : ℝ) := h₀ x b
      -- Combine the two equalities to get f (f(x) + 3a) = f (f(x) + 3b).
      have h₂ (x : ℝ) : f (f x + 3 * a) = f (f x + 3 * b) := by
        rw [h₀a, h₀b, h]
      -- Prove that f(y) = f(y + 3(b - a)) for all y.
      have h₃ (y : ℝ) : f y = f (y + 3 * (b - a)) := by
        -- Choose x such that f(x) = y - 3a by surjectivity.
        obtain ⟨x, h₁⟩ := h₁ (y - 3 * a)
        apply add_eq_of_eq_sub at h₁
        rw [<-h₁, h₂ x]
        ring_nf
      -- In particular, f(0) = f(3(b - a)).
      have h₄ := h₃ 0
      simp at h₄
      -- Show that f(f(0)) = 12 * 3 * (b - a) + f(f(0)) and hence a = b by combining h₄ and the given functional equation.
      -- Specialize (x, y) = (3(b - a), 0) at h₀.
      specialize h₀ (3 * (b - a)) 0
      -- Use h₄ to simplify the equality.
      simp [<-h₄] at h₀
      -- Specialize y = f(0) - 3(b - a) in h₃.
      specialize h₃ (f 0 - 3 * (b - a))
      -- Use h₃ to simplify the equality.
      simp [h₃] at h₀
      -- Get a = b, hence proving injectivity.
      linarith only [h₀]
    -- Get f(y)=f(0)+3y by injectivity.
    have h₃ (y : ℝ) : f y = f 0 + 3 * y := by
      --- Specialize x = 0 in the original functional equation.
      specialize h₀ 0 y
      simp at h₀
      -- Use injectivity.
      apply h₂ at h₀
      exact h₀.symm
    -- Now use a = f(0) to get the specific form.
    use f 0
  . -- Show that this form of function does satisfy the functional equation.
    rintro ⟨a, h⟩
    -- Show that the function satisfies the functional equation.
    intro x y
    -- Use the specific form of f.
    rw [h, h, h, h]
    ring_nf