import Mathlib

theorem number_theory_137383 (n : ℕ) (h₀ : Odd n) (h₁ : ∏ i ∈ Finset.range 6, (n + 2 * i) = 135135) :
    n + (n + 2) + (n + 4) + (n + 6) + (n + 8) + (n + 10) = 48 := by
  have eq1 : n * (n + 2) * (n + 4) * (n + 6) * (n + 8) * (n + 10) = 135135 := by
    simp [Finset.prod_range_succ] at h₁
    nlinarith
  have h2 : n ≤ 21 := by
    by_contra h
    push_neg at h
    have hn1 : n ≥ 23 := by
      by_contra h'
      push_neg at h'
      have h7 : n ≤ 22 := by omega
      have h8 : n > 21 := by omega
      have h9 : n = 22 := by omega
      have h5 : n % 2 = 1 := by
        rcases h₀ with ⟨k, hk⟩
        omega
      have h10 : n % 2 = 0 := by
        omega
      omega
    have hn2 : n + 2 ≥ 25 := by omega
    have hn3 : n + 4 ≥ 27 := by omega
    have hn4 : n + 6 ≥ 29 := by omega
    have hn5 : n + 8 ≥ 31 := by omega
    have hn6 : n + 10 ≥ 33 := by omega
    have h3 : n * (n + 2) * (n + 4) * (n + 6) * (n + 8) * (n + 10) > 135135 := by
      have h4 : n * (n + 2) * (n + 4) * (n + 6) * (n + 8) * (n + 10) ≥ 23 * 25 * 27 * 29 * 31 * 33 := by
        have hn7 : n ≥ 23 := by linarith
        have hn8 : n + 2 ≥ 25 := by linarith
        have hn9 : n + 4 ≥ 27 := by linarith
        have hn10 : n + 6 ≥ 29 := by linarith
        have hn11 : n + 8 ≥ 31 := by linarith
        have hn12 : n + 10 ≥ 33 := by linarith
        have h5 : n * (n + 2) * (n + 4) * (n + 6) * (n + 8) * (n + 10) ≥ 23 * 25 * 27 * 29 * 31 * 33 := by
          apply Nat.mul_le_mul
          apply Nat.mul_le_mul
          apply Nat.mul_le_mul
          apply Nat.mul_le_mul
          apply Nat.mul_le_mul
          · linarith
          · linarith
          · linarith
          · linarith
          · linarith
          · linarith
        linarith
      have h5 : (23 * 25 * 27 * 29 * 31 * 33 : ℕ) > 135135 := by norm_num
      linarith [h4, h5]
    linarith [eq1, h3]
  have hn1 : n ≤ 21 := h2
  interval_cases n <;> norm_num at eq1 <;> omega