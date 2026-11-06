import Mathlib

theorem algebra_114355 (f : ℝ → ℝ) (hf : f = fun x => x^2 + abs x + 1) :
    {x | f x = 0}.encard = 0 := by

  have h1 : ∀ x : ℝ, f x ≠ 0 := by
    intro x
    rw [hf]
    simp
    have h2 : x^2 + abs x + 1 > 0 := by
      have h3 : x^2 ≥ 0 := sq_nonneg x
      have h4 : abs x ≥ 0 := abs_nonneg x
      linarith [abs_nonneg x, sq_nonneg x]
    intro h
    linarith [h2, h]

  have h2 : {x : ℝ | f x = 0} = ∅ := by
    ext x
    simp [h1]

  rw [h2]
  simp