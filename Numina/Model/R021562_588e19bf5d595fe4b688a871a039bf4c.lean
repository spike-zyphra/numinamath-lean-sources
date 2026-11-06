import Mathlib

open Real

theorem inequalities_33857 (x : ℝ) :
    (∀ n : ℕ, 0 < n → (1 + x) ^ n ≤ 1 + (2 ^ n - 1) * x) ↔ x ∈ Set.Icc 0 1 := by
  constructor
  · -- Assume the inequality holds for all positive n, prove x ∈ [0,1]
    intro h
    have h1 := h 2 (by norm_num)
    have h2 : 0 ≤ x := by
      norm_num at h1
      nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 1)]
    have h3 : x ≤ 1 := by
      norm_num at h1
      nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 1)]
    exact ⟨h2, h3⟩
  · -- Assume x ∈ [0,1], prove the inequality holds for all positive n
    rintro ⟨hx0, hx1⟩
    intro n hn
    have h : ∀ (n : ℕ), (1 + x) ^ n ≤ 1 + (2 ^ n - 1) * x := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        have h1 : (1 + x) ^ (n + 1 : ℕ) = (1 + x) ^ n * (1 + x) := by ring
        rw [h1]
        have h3 : (1 + x) ^ n * (1 + x) ≤ (1 + (2 ^ n - 1) * x) * (1 + x) := by
          apply mul_le_mul_of_nonneg_right
          linarith [ih]
          linarith
        have h4 : (1 + (2 ^ n - 1) * x) * (1 + x) ≤ 1 + (2 ^ (n + 1 : ℕ) - 1) * x := by
          have h4 : (1 + (2 ^ n - 1) * x) * (1 + x) = 1 + (2 ^ n - 1) * x + x + (2 ^ n - 1) * x ^ 2 := by
            ring
          rw [h4]
          have h6 : x ^ 2 ≤ x := by
            nlinarith
          have h7 : (2 ^ n - 1 : ℝ) * x ^ 2 ≤ (2 ^ n - 1 : ℝ) * x := by
            have h8 : (0 : ℝ) ≤ (2 ^ n - 1 : ℝ) := by
              have h10 : (2 : ℝ) ^ n ≥ (1 : ℝ) := by
                have h10 : (2 : ℝ) ^ (0 : ℕ) = 1 := by norm_num
                have h11 : (2 : ℝ) ^ n ≥ (2 : ℝ) ^ (0 : ℕ) := by
                  apply pow_le_pow_right
                  all_goals
                    norm_num
                nlinarith
              linarith
            nlinarith
          nlinarith [show (2 : ℝ) ^ (n + 1 : ℕ) = 2 * (2 : ℝ) ^ n by ring]
        linarith
    have h2 := h n
    have h3 : n > 0 := by linarith
    have h4 : n ≥ 1 := by omega
    simpa using h2