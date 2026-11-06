import Mathlib

theorem algebra_271487 (m n : ℤ) :
    ∃ k : ℕ, 0 < k ∧ (m + 3 * n - 1) / (m * n + 2 * n - m - 2) = k ↔
    (m, n) = (-1, 2) ∨ (m, n) = (-1, 0) ∨ (m, n) = (0, 3) ∨
    (m, n) = (0, -1) ∨ (m, n) = (1, 2) ∨ (m, n) = (2, 5) ∨
    (m, n) = (4, 3) := by
  by_cases h1 : (m, n) = (-1, 2) ∨ (m, n) = (-1, 0) ∨ (m, n) = (0, 3) ∨ (m, n) = (0, -1) ∨ (m, n) = (1, 2) ∨ (m, n) = (2, 5) ∨ (m, n) = (4, 3)
  · -- Case where (m, n) is one of the pairs in the solution set
    rcases h1 with (h | h | h | h | h | h | h)
    · -- Case (m, n) = (-1, 2)
      rw [Prod.mk.inj_iff] at h
      rcases h with ⟨rfl, rfl⟩
      use 4
      norm_num
    · -- Case (m, n) = (-1, 0)
      rw [Prod.mk.inj_iff] at h
      rcases h with ⟨rfl, rfl⟩
      use 2
      norm_num
    · -- Case (m, n) = (0, 3)
      rw [Prod.mk.inj_iff] at h
      rcases h with ⟨rfl, rfl⟩
      use 2
      norm_num
    · -- Case (m, n) = (0, -1)
      rw [Prod.mk.inj_iff] at h
      rcases h with ⟨rfl, rfl⟩
      use 1
      norm_num
    · -- Case (m, n) = (1, 2)
      rw [Prod.mk.inj_iff] at h
      rcases h with ⟨rfl, rfl⟩
      use 2
      norm_num
    · -- Case (m, n) = (2, 5)
      rw [Prod.mk.inj_iff] at h
      rcases h with ⟨rfl, rfl⟩
      use 1
      norm_num
    · -- Case (m, n) = (4, 3)
      rw [Prod.mk.inj_iff] at h
      rcases h with ⟨rfl, rfl⟩
      use 1
      norm_num
  · -- Case where (m, n) is not in the solution set
    push_neg at h1
    use 0
    simp at *
    <;> tauto