import Mathlib

theorem algebra_124680 (f : ℝ → ℕ) (hf : ∀ x, 0 < f x)
  (h : ∀ x y, f (x + 1 / f y) = f (y + 1 / f x)) :
  ¬Function.Surjective f := by
  intro h1
  have h2 : ∀ n : ℕ, ∃ x : ℝ, f x = n := by
    intro n
    simpa using h1 n
  have h3 : ∃ x : ℝ, f x = 0 := h2 0
  rcases h3 with ⟨x, hx⟩
  have h4 : 0 < f x := hf x
  omega