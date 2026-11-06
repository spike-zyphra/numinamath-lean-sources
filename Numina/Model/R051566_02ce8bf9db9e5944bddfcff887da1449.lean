import Mathlib

theorem algebra_284372 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 - 4 * x + 3) :
    IsLeast (Set.image f {x | x ∈ Set.univ}) (-1) := by
  have h1 : ∀ x, f x = (x - 2) ^ 2 - 1 := by
    intro x
    rw [hf]
    ring
  constructor
  · -- Show that -1 belongs to the image of f
    use 2
    simp [h1]
    all_goals norm_num
  · -- Show that -1 is the smallest in the image
    intro y
    intro hy
    rcases hy with ⟨x, hx⟩
    rw [h1] at hx
    have h2 : (x - 2) ^ 2 ≥ 0 := by 
      exact sq_nonneg (x - 2)
    linarith