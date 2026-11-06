import Mathlib

theorem number_theory_312604 (k : ℕ) (hk : 0 < k) :
    (∃ n, 0 < n ∧ n * (n + 1) = 25 * k + 6) ↔
    ∃ m, 0 < m ∧ m * (m + 1) = k := by
  constructor
  · -- Assume ∃ n, 0 < n ∧ n * (n + 1) = 25 * k + 6, prove ∃ m, 0 < m ∧ m * (m + 1) = k
    rintro ⟨n, hn, h1⟩
    have h3 : n % 5 = 2 := by
      by_cases h : n ≤ 5
      · interval_cases n <;> omega
      · -- n > 5
        have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
          omega
        rcases h4 with (h4 | h4 | h4 | h4 | h4)
        · -- n % 5 = 0
          have h5 : (n * (n + 1)) % 5 = 0 := by
            simp [Nat.mul_mod, Nat.add_mod, h4]
          have h6 : (25 * k + 6) % 5 = 1 := by
            omega
          have h7 : (n * (n + 1)) % 5 = (25 * k + 6) % 5 := by
            omega
          rw [h5] at h7
          omega
        · -- n % 5 = 1
          have h5 : (n * (n + 1)) % 5 = 2 := by
            simp [Nat.mul_mod, Nat.add_mod, h4]
          have h6 : (25 * k + 6) % 5 = 1 := by
            omega
          have h7 : (n * (n + 1)) % 5 = (25 * k + 6) % 5 := by
            omega
          rw [h5] at h7
          omega
        · -- n % 5 = 2
          have h5 : (n * (n + 1)) % 5 = 1 := by
            simp [Nat.mul_mod, Nat.add_mod, h4]
          have h6 : (25 * k + 6) % 5 = 1 := by
            omega
          have h7 : (n * (n + 1)) % 5 = (25 * k + 6) % 5 := by
            omega
          rw [h5] at h7
          omega
          <;> omega
        · -- n % 5 = 3
          have h5 : (n * (n + 1)) % 5 = 2 := by
            simp [Nat.mul_mod, Nat.add_mod, h4]
          have h6 : (25 * k + 6) % 5 = 1 := by
            omega
          have h7 : (n * (n + 1)) % 5 = (25 * k + 6) % 5 := by
            omega
          rw [h5] at h7
          omega
        · -- n % 5 = 4
          have h5 : (n * (n + 1)) % 5 = 0 := by
            simp [Nat.mul_mod, Nat.add_mod, h4]
          have h6 : (25 * k + 6) % 5 = 1 := by
            omega
          have h7 : (n * (n + 1)) % 5 = (25 * k + 6) % 5 := by
            omega
          rw [h5] at h7
          omega
    have h4 : ∃ m, n = 5 * m + 2 := by
      have h5 : n % 5 = 2 := h3
      have : ∃ m, n = 5 * m + 2 := by
        refine' ⟨n / 5, by omega⟩
      assumption
    rcases h4 with ⟨m, hm⟩
    have h4 : k = m * (m + 1) := by
      rw [hm] at h1
      nlinarith
    have hm1 : 0 < m := by
      by_contra h
      push_neg at h
      have h4' : m = 0 := by
        omega
      rw [h4'] at h4
      nlinarith
      all_goals linarith
    exact ⟨m, hm1, by linarith [h4]⟩
  · -- Assume ∃ m, 0 < m ∧ m * (m + 1) = k, prove ∃ n, 0 < n ∧ n * (n + 1) = 25 * k + 6
    rintro ⟨m, hm, h1⟩
    use 5 * m + 2
    constructor
    · -- Show n > 0
      nlinarith
    · -- Show n * (n + 1) = 25 * k + 6
      nlinarith [h1]