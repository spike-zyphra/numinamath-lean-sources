import Mathlib

theorem number_theory_324493 :
    Set.ncard {k : ℕ | 0 < k ∧ k ≤ 50 ∧ ∀ n : ℕ, 0 < n → 7 ∣ 2 * 3^(6 * n) + k * 2^(3 * n + 1) - 1} = 7 := by
  have h1 : {k : ℕ | 0 < k ∧ k ≤ 50 ∧ ∀ n : ℕ, 0 < n → 7 ∣ 2 * 3^(6 * n) + k * 2^(3 * n + 1) - 1} = {3, 10, 17, 24, 31, 38, 45} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- First direction: if k in the set, then k is one of the 7 values
      rintro ⟨hk1, hk2, hk⟩
      have h2 : ∀ n : ℕ, 0 < n → 7 ∣ 2 * 3^(6 * n) + k * 2^(3 * n + 1) - 1 := hk
      have h3 := h2 1 (by norm_num)
      norm_num at h3
      have h4 : k % 7 = 3 := by
        omega
      have h5 : k ≤ 50 := by
        omega
      have h6 : k % 7 = 3 := h4
      omega
    · -- Second direction: each given value is in the set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Show k = 3
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show divisibility
          intro n hn
          have h1 : ∀ n : ℕ, 0 < n → 7 ∣ 2 * 3^(6 * n) + 3 * 2^(3 * n + 1) - 1 := by
            intro n hn
            induction n with
            | zero => exfalso; linarith
            | succ n ih =>
              cases n with
              | zero => norm_num
              | succ n =>
                norm_num [pow_succ, pow_mul] at ih ⊢
                all_goals omega
          apply h1 n hn
      · -- Show k = 10
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show divisibility
          intro n hn
          have h1 : ∀ n : ℕ, 0 < n → 7 ∣ 2 * 3^(6 * n) + 10 * 2^(3 * n + 1) - 1 := by
            intro n hn
            induction n with
            | zero => exfalso; linarith
            | succ n ih =>
              cases n with
              | zero => norm_num
              | succ n =>
                norm_num [pow_succ, pow_mul] at ih ⊢
                all_goals omega
          apply h1 n hn
      · -- Show k = 17
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show divisibility
          intro n hn
          have h1 : ∀ n : ℕ, 0 < n → 7 ∣ 2 * 3^(6 * n) + 17 * 2^(3 * n + 1) - 1 := by
            intro n hn
            induction n with
            | zero => exfalso; linarith
            | succ n ih =>
              cases n with
              | zero => norm_num
              | succ n =>
                norm_num [pow_succ, pow_mul] at ih ⊢
                all_goals omega
          apply h1 n hn
      · -- Show k = 24
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show divisibility
          intro n hn
          have h1 : ∀ n : ℕ, 0 < n → 7 ∣ 2 * 3^(6 * n) + 24 * 2^(3 * n + 1) - 1 := by
            intro n hn
            induction n with
            | zero => exfalso; linarith
            | succ n ih =>
              cases n with
              | zero => norm_num
              | succ n =>
                norm_num [pow_succ, pow_mul] at ih ⊢
                all_goals omega
          apply h1 n hn
      · -- Show k = 31
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show divisibility
          intro n hn
          have h1 : ∀ n : ℕ, 0 < n → 7 ∣ 2 * 3^(6 * n) + 31 * 2^(3 * n + 1) - 1 := by
            intro n hn
            induction n with
            | zero => exfalso; linarith
            | succ n ih =>
              cases n with
              | zero => norm_num
              | succ n =>
                norm_num [pow_succ, pow_mul] at ih ⊢
                all_goals omega
          apply h1 n hn
      · -- Show k = 38
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show divisibility
          intro n hn
          have h1 : ∀ n : ℕ, 0 < n → 7 ∣ 2 * 3^(6 * n) + 38 * 2^(3 * n + 1) - 1 := by
            intro n hn
            induction n with
            | zero => exfalso; linarith
            | succ n ih =>
              cases n with
              | zero => norm_num
              | succ n =>
                norm_num [pow_succ, pow_mul] at ih ⊢
                all_goals omega
          apply h1 n hn
      · -- Show k = 45
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show divisibility
          intro n hn
          have h1 : ∀ n : ℕ, 0 < n → 7 ∣ 2 * 3^(6 * n) + 45 * 2^(3 * n + 1) - 1 := by
            intro n hn
            induction n with
            | zero => exfalso; linarith
            | succ n ih =>
              cases n with
              | zero => norm_num
              | succ n =>
                norm_num [pow_succ, pow_mul] at ih ⊢
                all_goals omega
          apply h1 n hn
  rw [h1]
  norm_num