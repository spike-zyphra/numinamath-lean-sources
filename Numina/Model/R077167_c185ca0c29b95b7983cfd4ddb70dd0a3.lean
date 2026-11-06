import Mathlib

theorem algebra_156175 (f : ℝ → ℝ) (hf : f = fun x => x + x ^ 2) :
    IsLeast (Set.range f) (f (-1 / 2)) := by
  have h1 : ∀ x, f x = x + x ^ 2 := by 
    intro x
    rw [hf]

  have h2 : f (-1 / 2) = -1 / 4 := by 
    rw [h1]
    norm_num

  constructor
  · -- Show f(-1/2) is in the range of f, which is trivial.
    simpa using by norm_num

  · -- Show f(-1/2) ≤ y for all y in the range of f
    intro y
    rintro ⟨x, hx⟩

    rw [h1] at hx
    rw [h2]

    nlinarith [sq_nonneg (x + 1 / 2)]