import Mathlib


theorem algebra_308766 (n : ℕ) (hn : n > 0) :
    Even ((1 - (-1 : ℤ)^n) * (n^2 - 1) / 8) := by
  have h1 : n ≥ 1 := by linarith
  have h2 : ((1 - (-1 : ℤ) ^ n) * (n ^ 2 - 1) ) % 16 = 0 := by
    have h3 : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases h3 with (h3 | h3)
    · 
      have h4 : (-1 : ℤ) ^ n = 1 := by
        have : n % 2 = 0 := h3
        have h6 : ∃ k, n = 2 * k := by
          refine' ⟨n / 2, by omega⟩
        rcases h6 with ⟨k, hk⟩
        rw [show n = 2 * k by linarith]
        have h5 : ∀ k : ℕ, (-1 : ℤ) ^ (2 * k) = 1 := by
          intro k
          induction k with
          | zero => norm_num
          | succ k ih =>
            simp [pow_succ, pow_mul, mul_add] at ih ⊢
            all_goals omega
        apply h5 k
      have h8 : (1 - (-1 : ℤ) ^ n) * (n ^ 2 - 1) = 0 := by
        rw [h4]
        norm_num
      rw [h8]
      all_goals
        norm_num
    ·
      have h4 : (-1 : ℤ) ^ n = -1 := by
        have : n % 2 = 1 := h3
        have h6 : ∃ k, n = 2 * k + 1 := by
          have h7 : n % 2 = 1 := h3
          have h8 : n ≥ 1 := by omega
          refine' ⟨(n - 1) / 2, by omega⟩
        rcases h6 with ⟨k, hk⟩
        rw [show n = 2 * k + 1 by linarith]
        have h5 : ∀ k : ℕ, (-1 : ℤ) ^ (2 * k + 1) = -1 := by
          intro k
          induction k with
          | zero => norm_num
          | succ k ih =>
            simp [pow_succ, pow_mul, mul_add] at ih ⊢
            all_goals omega
        apply h5 k
      have h10 : n % 2 = 1 := by omega
      have h14 : (n : ℤ) % 8 = 1 ∨ (n : ℤ) % 8 = 3 ∨ (n : ℤ) % 8 = 5 ∨ (n : ℤ) % 8 = 7 := by
        have h15 : n % 2 = 1 := h3
        omega
      have h18 : ((n : ℤ) ^ 2) % 8 = 1 := by
        rcases h14 with (h | h | h | h)
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h]
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h]
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h]
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h]
      have h22 : ((n : ℤ) ^ 2 - 1) % 8 = 0 := by
        omega
      have h26 : (1 - (-1 : ℤ) ^ n) * (n ^ 2 - 1) % 16 = 0 := by
        have h27 : (1 - (-1 : ℤ) ^ n) = 2 := by
          rw [h4]
          norm_num
        rw [h27]
        have h28 : ((2 : ℤ) * (n ^ 2 - 1)) % 16 = 0 := by
          have h31 : 16 ∣ (2 : ℤ) * (n ^ 2 - 1) := by
            have h32 : 8 ∣ (n ^ 2 - 1 : ℤ) := by
              omega
            have h33 : 16 ∣ (2 : ℤ) * (n ^ 2 - 1) := by
              obtain ⟨k, hk⟩ := h32
              use k
              linarith
            exact h33
          have h34 : (2 : ℤ) * (n ^ 2 - 1) % 16 = 0 := by
            omega
          assumption
        assumption
      assumption
  have h4 : ((1 - (-1 : ℤ) ^ n) * (n ^ 2 - 1) / 8) % 2 = 0 := by
    omega
  exact ⟨( (1 - (-1 : ℤ) ^ n) * (n^2 - 1) / 8) / 2, by omega⟩