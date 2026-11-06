import Mathlib

theorem number_theory_626340 : {Nat.ofDigits 10 [d, c, b, a] | (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (_ : 0 < a ∧ a ≤ 9 ∧ b ≤ 9 ∧ 0 < c ∧ c ≤ 9 ∧ d ≤ 9) (_ : (Nat.ofDigits 10 [b, a] + Nat.ofDigits 10 [d, c]) ^ 2 = Nat.ofDigits 10 [d, c, b, a])} = {2025, 3025} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume n in LHS, prove in RHS
    rintro ⟨a, b, c, d, ⟨ha1, ha2, hb1, hc1, hc2, hd1⟩, h_eq⟩
    simp [Nat.ofDigits, List.foldl] at h_eq
    have h1 : a > 0 := by linarith
    have h2 : a ≤ 9 := by linarith
    have h3 : b ≤ 9 := by linarith
    have h4 : c > 0 := by linarith
    have h5 : c ≤ 9 := by linarith
    have h6 : d ≤ 9 := by linarith

    have h7 : (10 * a + b + 10 * c + d) ^ 2 = 1000 * a + 100 * b + 10 * c + d := by
      nlinarith

    have h8 : (10 * a + b + 10 * c + d) ≤ 99 := by
      nlinarith [sq_nonneg (10 * a + b + 10 * c + d - 100 : ℕ), sq_nonneg (10 * a + b + 10 * c + d : ℕ), sq_nonneg (a * 10 + b + c * 10 + d : ℕ)]
    
    have h9 : (10 * a + b + 10 * c + d) ≥ 32 := by
      nlinarith [sq_nonneg (10 * a + b + 10 * c + d : ℕ), sq_nonneg (10 * a + b + 10 * c + d - 31 : ℕ)]
    
    interval_cases h : (10 * a + b + 10 * c + d) <;> try { 
      omega
    }
  · -- Assume n in RHS, prove in LHS
    rintro (rfl | rfl)
    · -- n = 2025
      use 2, 0, 2, 5
      native_decide
    · -- n = 3025
      use 3, 0, 2, 5
      native_decide