import Mathlib

theorem algebra_21894 : (Nat.card {n : ℕ | ∃ k, n = k^2 ∧ n ∈ Finset.Icc 1 100}) / 100 = 1 / 10 := by
  have h1 : {n : ℕ | ∃ k, n = k^2 ∧ n ∈ Finset.Icc 1 100} = {1, 4, 9, 16, 25, 36, 49, 64, 81, 100} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First direction: if n is a perfect square in [1, 100], it is in the singleton set
      rintro ⟨k, rfl, hk1, hk2⟩
      have h2 : k ≤ 10 := by nlinarith
      interval_cases k <;> norm_num at *
      <;> tauto
    · -- Second direction: if n is in the singleton set, it is a perfect square in [1, 100]
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- 1 is 1^2
        exact ⟨1, by norm_num, by norm_num⟩
      · -- 4 is 2^2
        exact ⟨2, by norm_num, by norm_num⟩
      · -- 9 is 3^2
        exact ⟨3, by norm_num, by norm_num⟩
      · -- 16 is 4^2
        exact ⟨4, by norm_num, by norm_num⟩
      · -- 25 is 5^2
        exact ⟨5, by norm_num, by norm_num⟩
      · -- 36 is 6^2
        exact ⟨6, by norm_num, by norm_num⟩
      · -- 49 is 7^2
        exact ⟨7, by norm_num, by norm_num⟩
      · -- 64 is 8^2
        exact ⟨8, by norm_num, by norm_num⟩
      · -- 81 is 9^2
        exact ⟨9, by norm_num, by norm_num⟩
      · -- 100 is 10^2
        exact ⟨10, by norm_num, by norm_num⟩
  rw [h1]
  norm_num