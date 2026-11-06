import Mathlib

/- Two linear functions $f(x)$ and $g(x)$ satisfy the properties that for all $x$,

- $f(x)+g(x)=2$
- $f(f(x))=g(g(x))$
and $f(0)=2022$. Compute $f(1)$.-/
theorem algebra_610529 (f g : ℤ → ℤ) (h₀ : ∀ x, f x + g x = 2) (h₁ : ∀ x, f (f x) = g (g x)) (h₂ : f 0 = 2022) (h₃ : ∃ k l, ∀ x, f x = k * x + l) (h₄ : ∃ k l, ∀ x, g x = k * x + l) : f 1 = 1 := by
  obtain ⟨a, b, h₃⟩ := h₃
  obtain ⟨c, d, h₄⟩ := h₄
  -- First find that g(0) = -2020.
  have h₅ : g 0 = -2020 := by
    have : f 0 + g 0 = 2 := h₀ 0
    rw [h₂] at this
    linarith
  -- Solve that b = 2022.
  have h₆ : b = 2022 := by
    linarith only [h₂, h₃ 0]
  -- Solve that d = -2020.
  have h₇ : d = -2020 := by
    linarith only [h₅, h₄ 0]
  subst h₆ h₇
  -- Substitute linarity condition of f and g into other equations.
  replace h₀ (x : ℤ) : (a + c) * x + 2 = 2 := by
    linarith only [h₃ x, h₄ x, h₀ x]
  replace h₁ (x : ℤ) : a ^ 2 * x + (a + 1) * 2022 = c ^ 2 * x - (c + 1) * 2020 := by
    specialize h₁ x
    iterate 2 rw [h₃, h₄] at h₁
    linarith only [h₁]
  -- Show that a + c = 0 by h₀.
  have h₈ : a + c = 0 := by
    linarith only [h₀ 1]
  -- Find the relation of a and c by substituting x = 0 at h₁.
  specialize h₁ 0
  simp at h₁
  -- Find out that a = -2021 by combining the two results above.
  have h₉ : a = -2021 := by
    linarith only [h₈, h₁]
  -- Directly compute f(1) using h₃.
  linarith only [h₃ 1, h₉]
  