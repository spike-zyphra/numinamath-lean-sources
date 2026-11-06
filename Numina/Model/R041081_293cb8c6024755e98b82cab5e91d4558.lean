import Mathlib

theorem number_theory_320270 :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ ¬∃ m : ℤ, m^3 = n ∧
      ∃ a b c : ℝ, a = n ^ ((1 : ℝ) / 3) ∧
        b = 1 / (a - ⌊a⌋) ∧ c = 1 / (b - ⌊b⌋) ∧
      ∃ r s t : ℤ, (r ≠ 0 ∨ s ≠ 0 ∨ t ≠ 0) ∧ r * a + s * b + t * c = 0 := by
  -- intro the N and use n = (N + 1)^3 + 1
  intro N
  use (N + 1) ^ 3 + 1
  constructor
  · -- Show that n > N
    have h1 : (N + 1) ^ 3 + 1 > (N : ℕ) := by
      have h2 : (N + 1 : ℕ) ^ 3 ≥ (N + 1 : ℕ) := by
        have h3 : (N + 1 : ℕ) ≥ (1 : ℕ) := by linarith
        have h4 : (N + 1 : ℕ) ^ 3 ≥ (N + 1 : ℕ) ^ 1 := by apply Nat.pow_le_pow_of_le_right; linarith; linarith
        simp at h4 ⊢
        linarith
      omega
    linarith
  · -- Show that not exists integer m
    intro h
    rcases h with ⟨m, hm⟩
    -- a, b, c exist
    rcases hm with ⟨hm1, a, b, c, ha1, hb1, hc1, r, s, t, h0, heq⟩
    -- to derive a contradiction
    have h1 : m^3 = (N + 1) ^ 3 + 1 := by
      have ht1 : (m^3 : ℤ) = (N + 1) ^ 3 + 1 := by
        have ht1 : (m^3 : ℤ) = ((N + 1) ^ 3 + 1 : ℕ) := by
          rw [hm1]
          all_goals norm_num
        norm_cast at ht1 ⊢
      ring_nf at ht1 ⊢
      linarith
    have h2 : m^3 > (N + 1 : ℤ) ^ 3 := by
      nlinarith
    have h3 : m > (N + 1 : ℤ) := by
      by_contra h
      push_neg at h
      have h4 : m ≤ (N + 1 : ℤ) := by linarith
      have h5 : m^3 ≤ (N + 1 : ℤ) ^ 3 := by
        have h6 : m - (N + 1) ≤ 0 := by omega
        have h7 : m^3 - (N + 1) ^ 3 = (m - (N + 1)) * (m^2 + m * (N + 1) + (N + 1) ^ 2) := by ring
        have h8 : m^2 + m * (N + 1) + (N + 1) ^ 2 ≥ 0 := by
          nlinarith [sq_nonneg (m + (N + 1 : ℤ) / 2), sq_nonneg (m), sq_nonneg ((N + 1 : ℤ) ) ]
        have h9 : (m - (N + 1 : ℤ) ) * (m^2 + m * (N + 1 : ℤ) + (N + 1 : ℤ) ^ 2) ≤ 0 := by
          nlinarith
        nlinarith
      nlinarith
    have h4 : m^3 < (m + 1: ℤ) ^ 3 := by
      nlinarith [sq_nonneg (m + 1: ℤ), sq_nonneg ((N + 1: ℤ) ), sq_nonneg (m - (m + 1: ℤ) ) ]
    nlinarith [sq_nonneg ((m - (N + 1): ℤ) ), sq_nonneg ((m + 1 - (N + 1) : ℤ) ), sq_nonneg ((m - (N + 1): ℤ) * (m - (N + 1): ℤ) ), sq_nonneg (m), sq_nonneg ((N + 1): ℤ) ]