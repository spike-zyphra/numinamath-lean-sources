import Mathlib

theorem number_theory_3911 : {(x, y) : ℕ × ℕ | 20 * x + 23 * y = 2023}.encard = 5 := by
  have h1 : {(x, y) : ℕ × ℕ | 20 * x + 23 * y = 2023} = {(100, 1), (77, 21), (54, 41), (31, 61), (8, 81)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- First, we verify that the given pairs satisfy the equation
      rintro H
      have h2 : x ≤ 101 := by omega
      have h3 : y ≤ 97 := by omega
      interval_cases y <;> omega
    · -- Now, we verify that these are the only pairs
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try native_decide