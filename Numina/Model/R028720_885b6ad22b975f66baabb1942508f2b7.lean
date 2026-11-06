import Mathlib

theorem number_theory_10843 :
    {n : ℕ | 0 < n ∧ 3 ∣ n * 2 ^ n + 1} = {n | 0 < n ∧ (n % 6) = 1 ∨ (n % 6) = 2} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume `0 < n ∧ 3 ∣ n * 2 ^ n + 1`, prove `0 < n ∧ (n % 6) = 1 ∨ (n % 6) = 2`
    intro h
    rcases h with ⟨hn_pos, hdiv⟩
    have h1 : n > 0 := hn_pos
    have h2 : (n * 2 ^ n + 1) % 3 = 0 := by
      omega
    have h3 : n % 2 = 1 ∨ n % 2 = 0 := by omega
    rcases h3 with (h3 | h3)
    · -- n is odd
      have h4 : n % 2 = 1 := h3
      have h5 : (2 ^ n) % 3 = 2 := by
        have h9 : n % 2 = 1 := h3
        have h10 : ∃ k, n = 2 * k + 1 := by
          refine ⟨ (n - 1) / 2, by omega ⟩
        rcases h10 with ⟨k, hk⟩
        rw [hk]
        have h7 : ∀ k, (2 ^ (2 * k + 1)) % 3 = 2 := by
          intro k
          induction k with
          | zero => norm_num
          | succ k ih =>
            simp [Nat.pow_add, Nat.pow_mul, Nat.pow_mul, Nat.pow_add] at ih ⊢
            all_goals
              omega
        apply h7 k
      have h6 : (n * (2 ^ n)) % 3 = (n * 2) % 3 := by
        have h7 : (2 ^ n) % 3 = 2 := h5
        simp [Nat.mul_mod, h7]
      have h58 : (n * (2 ^ n) + 1) % 3 = 0 := h2
      have h8 : (n * 2) % 3 = 2 := by
        simp [Nat.add_mod, h6] at h58 ⊢
        omega
      have h9 : n % 3 = 1 := by
        omega
      have h14 : (n % 6 = 1) := by
        omega
      left
      tauto
    · -- n is even
      have h4 : n % 2 = 0 := h3
      have h5 : (2 ^ n) % 3 = 1 := by
        have h9 : n % 2 = 0 := h3
        have h10 : ∃ k, n = 2 * k := by
          refine ⟨n / 2, by omega⟩
        rcases h10 with ⟨k, hk⟩
        rw [hk]
        have h7 : ∀ k, (2 ^ (2 * k)) % 3 = 1 := by
          intro k
          induction k with
          | zero => norm_num
          | succ k ih =>
            simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
            all_goals
              omega
        apply h7 k
      have h6 : (n * (2 ^ n)) % 3 = (n) % 3 := by
        have h7 : (2 ^ n) % 3 = 1 := h5
        simp [Nat.mul_mod, h7]
      have h58 : (n * (2 ^ n) + 1) % 3 = 0 := h2
      have h9 : n % 3 = 2 := by
        simp [Nat.add_mod, h6] at h58 ⊢
        omega
      have h12 : (n % 6 = 2) := by
        omega
      simp [h12]
  · -- Assume `0 < n ∧ (n % 6) = 1 ∨ (n % 6) = 2`, prove `0 < n ∧ 3 ∣ n * 2 ^ n + 1`
    rintro (h | h)
    · -- 0 < n ∧ (n % 6) = 1
      rcases h with ⟨hn_pos, hn1⟩
      constructor
      · tauto
      · have h1 : n % 2 = 1 := by
          omega
        have h3 : n % 3 = 1 := by
          omega
        have h58 : (n * (2 ^ n) + 1) % 3 = 0 := by
          have h4 : (2 ^ n) % 3 = 2 := by
            have h7 : ∀ k, (2 ^ (2 * k + 1)) % 3 = 2 := by
              intro k
              induction k with
              | zero => norm_num
              | succ k ih =>
                simp [Nat.pow_add, Nat.pow_mul, Nat.pow_mul, Nat.pow_add] at ih ⊢
                all_goals
                  omega
            have h9 : ∃ k, n = 2 * k + 1 := by
              use (n - 1) / 2
              omega
            rcases h9 with ⟨k, hk⟩
            rw [hk]
            apply h7 k
          have h6 : (n * (2 ^ n)) % 3 = (n * 2) % 3 := by
            have h7 : (2 ^ n) % 3 = 2 := h4
            simp [Nat.mul_mod, h7]
          omega
        omega
    · -- (n % 6) = 2
      have hn1 : (n) % 6 = 2 := h
      have hn_pos : 0 < n := by
        omega
      constructor
      · tauto
      · have h1 : (n) % 2 = 0 := by
          omega
        have h58 : (n * (2 ^ n) + 1) % 3 = 0 := by
          have h43 : (2 ^ n) % 3 = 1 := by
            have h9 : n % 2 = 0 := by
              omega
            have h10 : ∃ k, n = 2 * k := by
              refine ⟨n / 2, by omega⟩
            rcases h10 with ⟨k, hk⟩
            rw [hk]
            have h7 : ∀ k, (2 ^ (2 * k)) % 3 = 1 := by
              intro k
              induction k with
              | zero => norm_num
              | succ k ih =>
                simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
                all_goals
                  omega
            apply h7 k
          have h6 : (n * (2 ^ n)) % 3 = (n) % 3 := by
            have h7 : (2 ^ n) % 3 = 1 := h43
            simp [Nat.mul_mod, h7]
          have h8 : (n) % 3 = 2 := by
            omega
          omega
        omega