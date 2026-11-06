import Mathlib

theorem number_theory_230631 :
    {n : ℕ | ∃ a b c d : ℕ,
    a < 10 ∧ b < 10 ∧ c < 10 ∧ d < 10 ∧
    n > 999 ∧ n < 10000 ∧
    b = a + 1 ∧ c = b + 1 ∧ d = c + 1 ∧
    [d, c, b, a] = Nat.digits 10 n ∧
    ∃ k : ℕ, Nat.ofDigits 10 [d, c, a, b] = k^2} = 
    {3456} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n in the left side, prove n = 3456
    rintro ⟨a, b, c, d, ha, hb, hc, hd, hn1, hn2, hb_eq, hc_eq, hd_eq, h1, k, hk⟩
    have h4 : Nat.digits 10 n = [d, c, b, a] := by
      rw [h1]
    have h5 : n = 1000 * a + 100 * b + 10 * c + d := by
      have h6 : n = Nat.ofDigits 10 (Nat.digits 10 n) := by
        rw [Nat.ofDigits_digits]
      rw [h4] at h6
      simp [Nat.ofDigits, mul_add, mul_comm, mul_assoc] at h6 ⊢
      omega
    have h7 : b = a + 1 := by linarith
    have h8 : c = a + 2 := by
      have hc1 : c = b + 1 := by linarith
      rw [h7] at hc1
      omega
    have h9 : d = a + 3 := by
      have hd1 : d = c + 1 := by linarith
      rw [h8] at hd1
      omega
    have h12 : Nat.ofDigits 10 [d, c, a, b] = d + 10 * c + 100 * a + 1000 * b := by
      simp [Nat.ofDigits, mul_add, mul_comm, mul_assoc]
      all_goals omega
    rw [h12] at hk
    have h30 : a ≤ 6 := by
      have h30 : d < 10 := by linarith
      rw [show d = a + 3 by linarith [h9]] at h30
      omega
    interval_cases a <;> try { 
      norm_num [h7, h8, h9] at hk h5
      all_goals
      have h31 : k ≤ 100 := by nlinarith
      interval_cases k <;> omega 
    }
  · -- Assume n = 3456 prove the existence of the numbers.
    intro hn
    rw [hn]
    use 3, 4, 5, 6
    constructor
    · norm_num  -- a < 10
    constructor
    · norm_num  -- b < 10
    constructor
    · norm_num  -- c < 10
    constructor
    · norm_num  -- d < 10
    constructor
    · norm_num  -- n > 999
    constructor
    · norm_num  -- n < 10000
    constructor
    · norm_num  -- b = a + 1
    constructor
    · norm_num  -- c = b + 1
    constructor
    · norm_num  -- d = c + 1
    constructor
    · native_decide
    · use 66
      native_decide