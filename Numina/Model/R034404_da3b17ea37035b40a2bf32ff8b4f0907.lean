import Mathlib


theorem number_theory_126604 (m n : ℕ) (hm : m > 0) (hn : n > 0)
    (h : 2^m - 1 = 3^n) : (m, n) = (2, 1) := by 
  have h1 : 2^m = 3^n + 1 := by 
    have h2 : 2^m ≥ 1 := by 
      have h3 : m ≥ 1 := by omega
      have h4 : 2^m ≥ 2^1 := by
        apply Nat.pow_le_pow_of_le_right (by norm_num) h3
      have h5 : 2^1 = 2 := by norm_num
      omega
    have h6 : 2^m = (2^m - 1) + 1 := by 
      omega
    rw [h6, h]
  have eq1 : m < 3 := by
    by_contra h3
    push_neg at h3
    have h3 : m ≥ 3 := by omega
    have h4 : (2^m) % 8 = 0 := by
      have h7 : m ≥ 3 := by linarith
      have h9 : ∀ (k : ℕ), (2 ^ (k + 3)) % 8 = 0 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [Nat.pow_add, Nat.pow_succ, Nat.mul_mod] at ih ⊢
          all_goals
            omega
      have h10 : m - 3 + 3 = m := by omega
      have h11 : m - 3 ≥ 0 := by omega
      have h12 : (2 ^ m) % 8 = 0 := by
        have h13 : m = (m - 3) + 3 := by omega
        rw [h13]
        apply h9 (m - 3)
      tauto
    have h9 : (3^n + 1) % 8 = 0 := by 
      omega
    have h10 : (3^n) % 8 = 7 := by 
      omega
    have h11 : (3^n) % 8 = 1 ∨ (3^n) % 8 = 3 := by
      have h12 : ∀ (k : ℕ), (3 ^ k) % 8 = 1 ∨ (3 ^ k) % 8 = 3 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          simp [Nat.pow_succ, Nat.mul_mod] at ih ⊢
          all_goals 
            omega
      specialize h12 n
      tauto
    omega
  have eq2 : m = 1 ∨ m = 2 := by
    have h22 : m < 3 := by linarith
    have h22 : m = 1 ∨ m = 2 := by 
      interval_cases m <;> tauto
    tauto
  rcases eq2 with (r | r)
  · 
    have h2 : m = 1 := r
    rw [show m = 1 by linarith] at h1
    have h3 : 3^n = 1 := by
      omega
    have h4 : n > 0 := by linarith
    have h5 : 3^n > 1 := by
      have h7 : n ≥ 1 := by linarith
      have h8 : 3^n ≥ 3^1 := by 
        apply Nat.pow_le_pow_of_le_right (by norm_num) (by linarith)
      have h9 : 3^1 = 3 := by norm_num
      omega
    omega
  · 
    have h2 : m = 2 := r
    rw [show m = 2 by linarith] at h1
    have h3 : 3^n = 3 := by
      omega
    have h4 : n = 1 := by
      have h12 : 3^n = 3 := by linarith
      have h13 : n = 1 := by
        exact Nat.pow_right_injective (by norm_num) h12
      linarith
    simp [h2, h4]