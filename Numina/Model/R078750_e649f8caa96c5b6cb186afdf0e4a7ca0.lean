import Mathlib

theorem algebra_5180 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 - 6 * x + 47) :
    IsLeast (Set.image f (Set.univ : Set ℝ)) 38 := by
  have h1 : ∀ x, f x = x^2 - 6*x + 47 := by simp [hf]

  constructor
  · -- Show that 38 belongs to the image of f
    use 3
    norm_num [h1]
  · -- Show that 38 is a lower bound
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h1 x] at hx
    have h2 : (x - 3) ^ 2 ≥ 0 := by
      apply sq_nonneg
    linarith [sq_nonneg (x - 3)]