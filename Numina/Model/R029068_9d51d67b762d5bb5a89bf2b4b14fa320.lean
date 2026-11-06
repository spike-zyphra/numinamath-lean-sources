import Mathlib

theorem number_theory_4890 (n : ℤ) : Even n ↔ n - 2 * ⌊n / 2⌋ = 0 := by
  constructor
  · -- Assume n is even, prove n - 2 * floor(n / 2) = 0
    intro h
    rcases h with ⟨k, hk⟩
    have h1 : ⌊n / 2⌋ = k := by
      rw [show (n : ℤ) = 2 * k by linarith]
      norm_num
      <;> omega
    rw [h1]
    have : (n : ℤ) = 2 * k := by
      linarith
    linarith
  · -- Assume n - 2 * floor(n / 2) = 0, prove n is even
    intro h
    have h1 : n = 2 * ⌊n / 2⌋ := by
      omega
    have h2 : Even n := by
      use ⌊n / 2⌋
      all_goals
        linarith
    exact h2