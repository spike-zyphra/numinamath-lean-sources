import Mathlib

theorem number_theory_4488 : {n : ℕ | n.Prime ∧ ∃ m, n = m ^ 3 + 1} = {2} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n is prime and exists m such that n = m^3 + 1, prove n = 2
    rintro ⟨hn, ⟨m, hn_eq⟩⟩
    by_cases h1 : m > 1
    · -- m > 1
      have h2 : m ^ 3 + 1 = (m + 1) * (m ^ 2 - m + 1) := by
        cases m with
        | zero => 
          all_goals norm_num at *
        | succ m =>
          cases m with
          | zero => 
            all_goals norm_num at *
          | succ m => 
            simp [pow_succ, pow_zero, mul_add, add_mul, Nat.add_comm, Nat.mul_assoc, mul_sub, Nat.sub_eq_zero_of_le] at *
            <;> ring_nf <;> omega
      have h3 : m + 1 > 1 := by omega
      have h4 : m ^ 2 - m + 1 > 1 := by
        have hm : m > 1 := h1
        have hm1 : m ≥ 2 := by omega
        have h5 : m ^ 2 ≥ m + 1 := by 
          nlinarith [sq_nonneg (m : ℕ), sq_nonneg ((m + 1 : ℕ)), sq_nonneg ((m - 1 : ℤ)), h1]
        have h8 : m ^ 2 - m + 1 > 1 := by
          have h9 : m ^ 2 - m ≥ 1 := by
            omega
          omega
        tauto
      have h5 : m ^ 3 + 1 = (m + 1) * (m ^ 2 - m + 1) := h2
      have h6 : (m + 1) > 1 := h3
      have h7 : (m ^ 2 - m + 1) > 1 := h4
      have h8 : ¬ n.Prime := by
        rw [hn_eq]
        rw [h5]
        apply Nat.not_prime_mul (by omega) (by omega)
      contradiction
    · -- m ≤ 1
      have h8 : m = 0 ∨ m = 1 := by 
        interval_cases m <;> omega
      rcases h8 with (h | h)
      · -- m = 0
        rw [h] at hn_eq
        all_goals norm_num at hn_eq
        all_goals norm_num [hn_eq] at hn
      · -- m = 1
        rw [h] at hn_eq
        all_goals norm_num at hn_eq
        all_goals omega
  · -- Assume n = 2, prove n is prime and exists m such that n = m^3 + 1
    intro hn
    rw [hn]
    constructor
    · -- Show 2 is prime
      norm_num
    · -- Show there exists m such that 2 = m^3 + 1
      use 1
      all_goals norm_num