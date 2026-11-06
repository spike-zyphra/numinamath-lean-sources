import Mathlib

theorem number_theory_188210 (m n : ℤ) :
    Even (m * n * (m + n)) := by
  have h1 : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have h2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h1 with (h1 | h1)
  · rcases h2 with (h2 | h2)
    · -- m even, n even
      have h3 : (m * n * (m + n)) % 2 = 0 := by
        simp [Int.mul_emod, Int.add_emod, h1, h2]
        <;> omega
      exact ⟨(m * n * (m + n)) / 2, by omega⟩
    · -- m even, n odd
      have h3 : (m * n * (m + n)) % 2 = 0 := by
        simp [Int.mul_emod, Int.add_emod, h1, h2]
        <;> omega
      exact ⟨(m * n * (m + n)) / 2, by omega⟩
  · rcases h2 with (h2 | h2)
    · -- m odd, n even
      have h3 : (m * n * (m + n)) % 2 = 0 := by
        simp [Int.mul_emod, Int.add_emod, h1, h2]
        <;> omega
      exact ⟨(m * n * (m + n)) / 2, by omega⟩
    · -- m odd, n odd
      have h3 : (m * n * (m + n)) % 2 = 0 := by
        simp [Int.mul_emod, Int.add_emod, h1, h2]
        <;> omega
      exact ⟨(m * n * (m + n)) / 2, by omega⟩