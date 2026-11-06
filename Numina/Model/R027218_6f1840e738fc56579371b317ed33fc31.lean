import Mathlib

theorem number_theory_292423 (k : ℕ) :
    ¬(k^6 + k^4 + k^2 = 10^(k + 1) + 9) := by
  intro h
  have eq1 : k ≤ 3 := by
    by_contra h1
    push_neg at h1
    have h2 : k ≥ 4 := by omega
    have h3 : k ^ 6 + k ^ 4 + k ^ 2 < 10 ^ (k + 1) := by
      have h4 : ∀ (n : ℕ), n ≥ 4 → n ^ 6 + n ^ 4 + n ^ 2 < 10 ^ (n + 1) := by
        intro n hn
        have base4 : 4 ^ 6 + 4 ^ 4 + 4 ^ 2 < 10 ^ (4 + 1) := by norm_num
        have step4 : ∀ (m : ℕ), m ≥ 4 → (m ^ 6 + m ^ 4 + m ^ 2 < 10 ^ (m + 1)) → (m + 1) ^ 6 + (m + 1) ^ 4 + (m + 1) ^ 2 < 10 ^ ((m + 1) + 1) := by
          intro m hm h7
          have h8 : (m + 1 : ℕ) ^ 6 + (m + 1 : ℕ) ^ 4 + (m + 1 : ℕ) ^ 2 < 10 ^ ((m + 1) + 1) := by
            have h10 : (m : ℕ) ^ 6 + (m : ℕ) ^ 4 + (m : ℕ) ^ 2 < 10 ^ (m + 1) := h7
            have h11 : (m + 1 : ℕ) ^ 6 + (m + 1 : ℕ) ^ 4 + (m + 1 : ℕ) ^ 2 ≤ 10 * ((m : ℕ) ^ 6 + (m : ℕ) ^ 4 + (m : ℕ) ^ 2) := by
              have h11 : m ≥ 4 := hm
              have h12 : (m + 1 : ℕ) ^ 6 ≤ 10 * (m : ℕ) ^ 6 := by
                have h13 : m ≥ 4 := hm
                nlinarith [sq_nonneg ((m : ℕ) ^ 3 : ℕ), sq_nonneg ((m + 1 : ℕ) ^ 3 : ℕ),
                      sq_nonneg ((m : ℕ) - 4 : ℤ), sq_nonneg ((m : ℕ) : ℕ),
                      mul_nonneg (show (0 : ℕ) ≤ (m) by omega) (show (0 : ℕ) ≤ (m) by omega),
                      mul_nonneg (show (0 : ℕ) ≤ (m) by omega) (show (0 : ℕ) ≤ (m) by omega),
                      sq_nonneg ((m : ℕ) ^ 2 : ℕ), sq_nonneg ((m + 1 : ℕ) ^ 2 : ℕ),
                      show (m : ℕ) ≥ 4 by omega]
              have h13 : (m + 1 : ℕ) ^ 4 ≤ 10 * (m : ℕ) ^ 4 := by
                have h13 : m ≥ 4 := hm
                nlinarith [sq_nonneg ((m : ℕ) ^ 2 : ℕ), sq_nonneg ((m + 1 : ℕ) ^ 2 : ℕ),
                      sq_nonneg ((m : ℕ) - 4 : ℤ), sq_nonneg ((m : ℕ) : ℕ),
                      mul_nonneg (show (0 : ℕ) ≤ (m) by omega) (show (0 : ℕ) ≤ (m) by omega),
                      mul_nonneg (show (0 : ℕ) ≤ (m) by omega) (show (0 : ℕ) ≤ (m) by omega),
                      sq_nonneg ((m : ℕ) ^ 2 : ℕ), sq_nonneg ((m + 1 : ℕ) ^ 2 : ℕ),
                      show (m : ℕ) ≥ 4 by omega]
              have h14 : (m + 1 : ℕ) ^ 2 ≤ 10 * (m : ℕ) ^ 2 := by
                have h13 : m ≥ 4 := hm
                nlinarith [sq_nonneg ((m : ℕ) : ℕ), sq_nonneg ((m + 1 : ℕ) : ℕ),
                      sq_nonneg ((m : ℕ) - 4 : ℤ), sq_nonneg ((m : ℕ) : ℕ),
                      mul_nonneg (show (0 : ℕ) ≤ (m) by omega) (show (0 : ℕ) ≤ (m) by omega),
                      mul_nonneg (show (0 : ℕ) ≤ (m) by omega) (show (0 : ℕ) ≤ (m) by omega),
                      sq_nonneg ((m : ℕ) ^ 2 : ℕ), sq_nonneg ((m + 1 : ℕ) ^ 2 : ℕ),
                      show (m : ℕ) ≥ 4 by omega]
              nlinarith
            have h12 : (m + 1 : ℕ) ^ 6 + (m + 1 : ℕ) ^ 4 + (m + 1 : ℕ) ^ 2 < 10 ^ ((m + 1) + 1) := by
              have h13 : 10 ^ ((m + 1) + 1) = 10 * (10 ^ (m + 1)) := by ring
              rw [h13]
              nlinarith [show (0 : ℕ) ≤ (10 ^ (m + 1) : ℕ) by positivity, h11, h10]
            linarith
          exact h8
        exact Nat.le_induction base4 step4 n hn
      specialize h4 k h2
      linarith
    have h4 : k ^ 6 + k ^ 4 + k ^ 2 < 10 ^ (k + 1) := h3
    omega
  have h7 : k ≤ 3 := eq1
  interval_cases k <;> norm_num at h