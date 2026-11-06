import Mathlib

theorem algebra_10613 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 + 10 * x + 21) :
    IsLeast (Set.range f) (-4) := by
  have h1 : ∀ x, f x = (x + 5) ^ 2 - 4 := by
    intro x
    rw [hf]
    ring

  have h2 : -4 ∈ Set.range f := by
    use -5
    rw [h1]
    norm_num

  have h3 : ∀ y, y ∈ Set.range f → -4 ≤ y := by
    intro y hy
    rcases hy with ⟨x, hx⟩
    have hfx : f x = (x + 5) ^ 2 - 4 := h1 x
    rw [show y = f x by linarith [hx, hfx]] 
    have h4 : (x + 5) ^ 2 ≥ 0 := by
      apply sq_nonneg
    linarith

  exact ⟨h2, h3⟩