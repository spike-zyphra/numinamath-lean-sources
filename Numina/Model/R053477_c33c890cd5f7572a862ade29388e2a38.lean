import Mathlib

theorem number_theory_258998 :
    ∃ a : ℕ, ∀ i ∈ Finset.range 5, Nat.Prime (a + 6 * i) ∧
    ∃ a : ℕ, ∀ i ∈ Finset.range 5, Nat.Prime (a + 12 * i) := by
  use 5
  intro i hi
  have h1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    simp [Finset.mem_range] at hi
    omega
  rcases h1 with (rfl | rfl | rfl | rfl | rfl)
  · constructor
    · norm_num
    · use 5
      intro i hi
      have h1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
        simp [Finset.mem_range] at hi
        omega
      rcases h1 with (rfl | rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  · constructor
    · norm_num
    · use 5
      intro i hi
      have h1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
        simp [Finset.mem_range] at hi
        omega
      rcases h1 with (rfl | rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  · constructor
    · norm_num
    · use 5
      intro i hi
      have h1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
        simp [Finset.mem_range] at hi
        omega
      rcases h1 with (rfl | rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  · constructor
    · norm_num
    · use 5
      intro i hi
      have h1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
        simp [Finset.mem_range] at hi
        omega
      rcases h1 with (rfl | rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  · constructor
    · norm_num
    · use 5
      intro i hi
      have h1 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
        simp [Finset.mem_range] at hi
        omega
      rcases h1 with (rfl | rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num