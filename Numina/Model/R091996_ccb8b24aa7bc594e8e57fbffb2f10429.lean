import Mathlib

theorem algebra_308180 {f : ℝ → ℝ} (h : ∀ x, f (x + 1) = -f x)
    (hf : ∀ x ∈ Set.Ioc 2 3, f x = x) :
    ∀ x ∈ Set.Ioc (-2) 0, x ∈ Set.Ioc (-2) (-1) → f x = x + 4 ∧
    x ∈ Set.Ioc (-1) 0 → f x = -x - 3 := by
  intro x hx hx1 h2
  rcases h2 with ⟨hfx, hx2⟩
  rcases hx1 with ⟨h2, h3⟩
  rcases hx2 with ⟨h4, h5⟩
  linarith