import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_8924 :
  IsLeast {x | ∃ a b : ℝ, x = a^4 + 4*a^3 + 8*a^2 + 4*a*b + 6*a + 4*b^2 + 10} 8 := by
  constructor
  · -- Show 8 is achievable
    use (-1)
    use (1 / 2)
    norm_num
  · -- Show there is no smaller value
    intro x
    rintro ⟨a, b, h_eq⟩
    have h1 : a^4 + 4*a^3 + 8*a^2 + 4*a*b + 6*a + 4*b^2 + 10 ≥ 8 := by
      nlinarith [sq_nonneg (b + a / 2), sq_nonneg (a^2 + 2 * a), sq_nonneg (a + 1)]
    linarith [h_eq, h1]