import Mathlib

theorem number_theory_301584 : ¬∃ n m, (2 ^ n * 3 ^ m - 1) = 12131 := by
  rintro ⟨n, m, h⟩
  have eq1 : 2 ^ n * 3 ^ m = 12132 := by
    omega
  have h1 : n ≤ 20 := by
    by_contra h2
    push_neg at h2
    have h21 : 2 ^ n ≥ 2 ^ 21 := by
      have : n ≥ 21 := by omega
      exact (pow_le_pow_right (by norm_num) this)
    have h22 : 2 ^ n * 3 ^ m ≥ 2 ^ 21 * 3 ^ 0 := by
      have h1 : 3 ^ m ≥ 3 ^ 0 := by
        have : m ≥ 0 := by linarith
        exact (pow_le_pow_right (by norm_num) this)
      nlinarith
    have : 2 ^ 21 * 3 ^ 0 ≥ 2 ^ 21 := by
      norm_num
    have h23 : 2 ^ n * 3 ^ m ≥ 2 ^ 21 := by
      nlinarith
    -- evaluate $2^{21}$ to be larger than 12132
    have h24 : (2 ^ 21 : ℕ) > 12132 := by
      norm_num
    nlinarith
  have h2 : m ≤ 10 := by
    by_contra h3
    push_neg at h3
    have h31 : 3 ^ m ≥ 3 ^ 11 := by
      have : m ≥ 11 := by omega
      exact (pow_le_pow_right (by norm_num) this)
    have h32 : 2 ^ n * 3 ^ m ≥ 2 ^ 0 * 3 ^ 11 := by
      have h1 : 2 ^ n ≥ 2 ^ 0 := by
        have : n ≥ 0 := by linarith
        exact (pow_le_pow_right (by norm_num) this)
      nlinarith
    have : 2 ^ 0 * 3 ^ 11 ≥ 3 ^ 11 := by
      norm_num
    have h33 : 2 ^ n * 3 ^ m ≥ 3 ^ 11 := by
      nlinarith
    -- evaluate $3^{11}$ to be larger than 12132
    have h34 : (3 ^ 11 : ℕ) > 12132 := by
      norm_num
    nlinarith
  interval_cases n <;> interval_cases m <;> omega