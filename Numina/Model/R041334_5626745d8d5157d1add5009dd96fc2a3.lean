import Mathlib

theorem number_theory_119531 (p : ℕ) (hp : Nat.Prime p) (h : 3 < p) :
    ∃ x y k : ℕ, 0 < 2 * k ∧ 2 * k < p ∧ x ^ 2 + y ^ 2 = p - 2 * k := by
  by_cases h1 : p > 5
  · -- Case p > 5
    have h2 : p % 2 = 1 := by
      by_contra h'
      push_neg at h'
      have h3 : p % 2 = 0 := by omega
      have h4 : ¬ Nat.Prime p := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals linarith
      tauto
    use 1, 2, (p - 5) / 2
    have hk : 2 * ((p - 5) / 2) = p - 5 := by
      have h4 : p % 2 = 1 := h2
      have h6 : (p - 5) % 2 = 0 := by
        omega
      have h7 : 2 * ((p - 5) / 2) = (p - 5) := by
        omega
      linarith
    have h4 : 0 < 2 * ((p - 5) / 2) := by
      omega
    have h5 : 2 * ((p - 5) / 2) < p := by
      omega
    constructor
    · linarith
    constructor
    · omega
    · -- Prove that 1^2 + 2^2 = p - 2k
      omega
  · -- Case p ≤ 5
    have h2 : p = 5 := by
      interval_cases p <;> norm_num at hp h ⊢
      <;> try { contradiction }
    rw [h2]
    use 1, 0, 2
    all_goals norm_num