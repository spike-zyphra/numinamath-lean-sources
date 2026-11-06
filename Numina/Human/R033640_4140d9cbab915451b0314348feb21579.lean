import Mathlib

/-Find all natural numbers $n$ for which there exists a rectangle whose side lengths are natural numbers, its perimeter is equal to $n$ and numerically equal to its area.-/
theorem number_theory_137238 (n : ℕ) :
    ∃ a b, a > 0 ∧ b > 0 ∧ n = 2 * (a + b) ∧ n = a * b ↔ n = 16 ∨ n = 18 := by
  by_cases h16 : n = 16
  · -- If n = 16, we use a = 4 and b = 4
    use 4, 4
    constructor
    · -- Assume the conditions hold, we need to prove n = 16 ∨ n = 18
      intro h
      rcases h with ⟨ha, hb, h1, h2⟩
      omega
    · -- Assume n = 16 ∨ n = 18, we need to prove the conditions
      rintro (h | h)
      · -- n = 16
        rw [h]
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- n = 18, but with a = 4, b = 4, this leads to a contradiction
        exfalso
        omega
  · -- n ≠ 16
    by_cases h18 : n = 18
    · -- If n = 18, we use a = 3 and b = 6
      use 3, 6
      constructor
      · -- Assume the conditions hold, we need to prove n = 16 ∨ n = 18
        intro h
        rcases h with ⟨ha, hb, h1, h2⟩
        omega
      · -- Assume n = 16 ∨ n = 18, we need to prove the conditions
        rintro (h | h)
        · -- n = 16, but with a = 3, b = 6, this leads to a contradiction
          exfalso
          omega
        · -- n = 18
          rw [h]
          constructor
          · norm_num
          constructor
          · norm_num
          constructor
          · norm_num
          · norm_num
    · -- n ≠ 16 and n ≠ 18
      use 0, 0
      simp [h16, h18]