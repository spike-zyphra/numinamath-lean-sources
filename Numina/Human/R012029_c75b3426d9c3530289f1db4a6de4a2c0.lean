import Mathlib

open Polynomial Complex

/- Find an ordered pair $(a, b)$ of real numbers for which $x^{2}+a x+b$ has a non-real root whose cube is 343 . -/
theorem algebra_170201 :
    ∃ a b : ℝ, ∃ x : ℂ, x ∉ Set.range ofReal ∧ x ^ 3 = 343 ∧ x ^ 2 + a * x + b = 0 := by
  -- X ^ 3 - 343 = (X - 7)(X ^ 2 + 7 * X + 49)
  -- So we set a = 7, b = 49
  use 7, 49
  simp
  -- We need to show that the polynomial has a non-real root
  let p : ℂ[X] := X ^ 2 + 7 * X + 49
  -- The polynomial has degree 2
  have hp : degree p = 2 := by
    simp [p]
    compute_degree!
  -- By the fundamental theorem of algebra, the polynomial has a complex root
  obtain ⟨z, hz⟩ := exists_root (show 0 < degree p by simp [hp])
  simp [p] at hz
  -- We need to show that the root is not real
  use z
  refine ⟨?_, ?_, hz⟩
  . -- If the root is real
    rintro x rfl
    -- Cast to real
    replace hz : x ^ 2 + 7 * x + 49 = 0 := by
      apply Complex.ofReal_injective
      simpa using hz
    -- But it is not possible since the discriminant is negative
    nlinarith
  . -- Since z ^ 2 + 7 * z + 49 = 0, we have z ^ 3 = (z - 7)(z ^ 2 + 7 * z + 49) + 343 = 343
    linear_combination (z - 7) * hz
