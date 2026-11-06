import Mathlib

theorem algebra_264815 (a : ℤ) :
    ∃ x : ℤ, a * (x ^ 2 + x) = 3 * (x ^ 2 + 1) ↔ a = 3 ∨ a = 5 := by
  by_cases h : a = 3
  · -- if a = 3, x=1
    use 1
    rw [h]
    norm_num
  · -- If a = 5, x = -3
    by_cases h2 : a = 5
    · -- if a = 5, x = -3
      use -3
      rw [h2]
      norm_num
    · -- If a ≠3 and a ≠5
      use 0
      constructor
      · -- Proof of the forward implication
        intro h_eq
        have h1 : a * (0 ^ 2 + (0 : ℤ)) = 3 * (0 ^ 2 + 1) := by
          simpa using h_eq
        norm_num at h1
      · -- Proof of the reverse implication
        rintro (h3 | h4)
        · -- Contradiction because a ≠ 3
          exfalso
          exact h h3
        · -- Contradiction because a ≠ 5
          exfalso
          exact h2 h4