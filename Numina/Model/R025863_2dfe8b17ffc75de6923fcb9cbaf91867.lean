import Mathlib

theorem number_theory_292163 (m n : ℕ) :
    2 ∣ (5 * m + n + 1) ∨ 2 ∣ (3 * m - n + 4) := by
  have h1 : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have h2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h1 with (h | h)
  · -- m is even
    rcases h2 with (h2 | h2)
    · -- n is even
      -- Show that 2 divides (3 * m - n + 4)
      have h3 : (3 * m - n + 4) % 2 = 0 := by 
        omega
      right
      omega
    · -- n is odd
      -- Show that 2 divides (5 * m + n + 1)
      have h3 : (5 * m + n + 1) % 2 = 0 := by 
        omega
      left
      omega
  · -- m is odd
    rcases h2 with (h2 | h2)
    · -- n is even
      -- Show that 2 divides (5 * m + n + 1)
      have h3 : (5 * m + n + 1) % 2 = 0 := by 
        omega
      left
      omega
    · -- n is odd
      -- Show that 2 divides (3 * m - n + 4)
      have h3 : (3 * m - n + 4) % 2 = 0 := by 
        omega
      right
      omega