import Mathlib

theorem number_theory_81030 (m : ℕ) (hm : 1000 ≤ m ∧ m ≤ 2021) :
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ, k^2 = m * n ∧ Nat.Prime (m - n) ↔
    m = 1156 ∨ m = 1296 ∨ m = 1369 ∨ m = 1600 ∨ m = 1764 := by
  by_cases h : m = 1156 ∨ m = 1296 ∨ m = 1369 ∨ m = 1600 ∨ m = 1764
  · -- There exists an element in the boxed answer
    rcases h with (r | r | r | r | r)
    · -- Case for m = 1156
      rw [r]
      use 1089
      constructor
      · norm_num
      use 1122
      all_goals norm_num
    · -- Case for m = 1296
      rw [r]
      use 1225
      constructor
      · norm_num
      use 1260
      all_goals norm_num
    · -- Case for m = 1369
      rw [r]
      use 1296
      constructor
      · norm_num
      use 1332
      all_goals norm_num
    · -- Case for m = 1600
      rw [r]
      use 1521
      constructor
      · norm_num
      use 1560
      all_goals norm_num
    · -- Case for m = 1764
      rw [r]
      use 1681
      constructor
      · norm_num
      use 1722
      all_goals norm_num
  · -- When none of the cases match, need to use contradiction
    push_neg at h
    use m + 1
    constructor
    · -- Show n > 0
      omega
    use 0
    simp at *
    <;> norm_num at h ⊢ <;> all_goals omega