import Mathlib

theorem number_theory_183598 : {k | ∃ m n, k = (3^m + 7^n) % 10} = {0, 2, 4, 6, 8} := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume k is in the left side, need to show it's in the right side
    rintro ⟨m, n, hk⟩
    have h1 : k = (3^m + 7^n) % 10 := by omega
    have h3 : k % 2 = 0 := by
      have h5 : (3^m + 7^n) % 2 = 0 := by
        have h1 : (3^m) % 2 = 1 := by
          have h11 : ∀ (m : ℕ), (3^m) % 2 = 1 := by
            intro m
            induction m with
            | zero =>
              simp
            | succ m ih =>
              simp [Nat.pow_succ, Nat.mul_mod, ih]
          apply h11 m
        have h2 : (7^n) % 2 = 1 := by
          have h22 : ∀ (n : ℕ), (7^n) % 2 = 1 := by
            intro n
            induction n with
            | zero =>
              simp
            | succ n ih =>
              simp [Nat.pow_succ, Nat.mul_mod, ih]
          apply h22 n
        omega
      omega
    have h4 : k % 2 = 0 := h3
    have h3 : k ≤ 9 := by
      omega
    interval_cases k <;> tauto
  · -- Show that each element in the right side is in the left side
    rintro (rfl | rfl | rfl | rfl | rfl)
    · -- k = 0
      use 1, 1
      all_goals
        norm_num
    · -- k = 2
      use 1, 2
      all_goals
        norm_num
    · -- k = 4
      use 1, 0
      all_goals
        norm_num
    · -- k = 6
      use 1, 3
      all_goals
        norm_num
    · -- k = 8
      use 0, 1
      all_goals
        norm_num