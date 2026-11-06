import Mathlib

set_option maxHeartbeats 1000000

theorem algebra_223772 (n : ℕ)
  (hn : n ≥ 10)
  (f : ℕ → ℝ)
  (hf : ∀ k ∈ Finset.range (n + 1), f k = (n.choose k) * (2/5 : ℝ)^k * (1/5 : ℝ)^(n-k)) :
  (∀ k ∈ Finset.range (n + 1), k ≠ 9 → f k < f 9)
  ↔ n = 13 := by

  constructor
  . intro hk

    have : 25 < 2 * n := by
      have h8:= hk 8 (by simp; omega)
      rw [hf , hf] at h8
      . field_simp at h8
        rw [← pow_add, ← pow_add] at h8
        rw [show 8 + (n - 8) = n by omega] at h8
        rw [show 9 + (n - 9) = n by omega] at h8
        have hpos1: (0 : ℝ) < (5 : ℝ) ^ n := by positivity
        rw [div_lt_iff₀ hpos1] at h8
        field_simp at h8
        rw [show (2:ℝ)^9 = 2*2^8 by norm_num] at h8
        have hpos2 : (0 : ℝ) < 2 ^ 8 := by norm_num
        rw [← lt_div_iff₀ hpos2] at h8
        rw [← mul_assoc] at h8
        field_simp at h8
        norm_cast at h8

        have h8 :  n.choose 8 * 9 < n.choose 9 * 9 * 2 := by linarith
        have := Nat.choose_succ_right_eq n 8
        norm_num at this
        rw [this] at h8
        rw [mul_assoc] at h8

        have hpos3 : 0 < n.choose 8 := by
          apply Nat.choose_pos
          omega
        rw [mul_lt_mul_left hpos3] at h8
        omega

      . simp; omega
      . simp; omega

    have : n < 14 := by
      have h10:= hk 10 (by simp; omega)
      rw [hf, hf] at h10
      . field_simp at h10
        rw [← pow_add, ← pow_add] at h10
        rw [show 10 + (n - 10) = n by omega] at h10
        rw [show 9 + (n - 9) = n by omega] at h10
        have hpos1: (0 : ℝ) < (5 : ℝ) ^ n := by positivity
        rw [div_lt_iff₀ hpos1] at h10
        field_simp at h10
        rw [show (2:ℝ)^10 = 2*2^9 by norm_num] at h10
        have hpos2 : (0 : ℝ) < 2 ^ 9 := by norm_num
        rw [← mul_assoc, ← lt_div_iff₀ hpos2] at h10
        field_simp at h10
        norm_cast at h10
        have h10 :  n.choose 10 * 10 * 2 < n.choose 9 * 10 := by linarith
        have := Nat.choose_succ_right_eq n 9
        norm_num at this
        rw [this] at h10
        rw [mul_assoc] at h10
        have hpos3 : 0 < n.choose 9 := by
          apply Nat.choose_pos
          omega
        rw [mul_lt_mul_left hpos3] at h10
        omega
      . simp; omega
      . simp; omega


    have : n = 13 := by omega
    exact this

  . intro hn k hk
    subst n
    simp at hk
    rw [hf, hf]
    . interval_cases k
      all_goals simp [Nat.choose_eq_factorial_div_factorial]
      all_goals
      . norm_cast
        repeat rw [Nat.factorial_succ]
        norm_num

    . simp
    . simp; exact hk
