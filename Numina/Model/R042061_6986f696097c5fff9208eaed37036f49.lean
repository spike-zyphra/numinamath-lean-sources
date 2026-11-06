import Mathlib

theorem number_theory_14445 (S : ℕ → ℕ) (hS : ∀ n, S n = (Nat.digits 10 n).sum)
    (t : Set ℕ) (ht : t = {m : ℕ | ∃ n : ℕ, S n = 1274 ∧ m = S (n + 1)}) :
    1239 ∈ t ∧ 1 ∉ t ∧ 3 ∉ t ∧ 12 ∉ t ∧ 1265 ∉ t := by
  constructor
  · -- Prove 1239 ∈ t
    rw [ht]
    use (10 ^ 1238 - 1) / 9 * (10 ^ 4) + 9999
    constructor
    · -- Show that S n = 1274
      rw [hS]
      native_decide
    · -- Show that m = S (n + 1)
      rw [hS]
      native_decide
  constructor
  · -- Show that 1 ∉ t
    intro h
    rw [ht] at h
    rcases h with ⟨m, hm1, hm2⟩
    rw [hS] at hm1
    rw [hS] at hm2
    have h1 : m % 9 = 5 := by
      have h_eq : (Nat.digits 10 m).sum = 1274 := hm1
      have h1 : m % 9 = 5 := by 
        have h_eq1 : m % 9 = (Nat.digits 10 m).sum % 9 := by
          rw [Nat.modEq_nine_digits_sum (m)]
        rw [h_eq] at h_eq1
        omega 
      exact h1
    -- S(m+1) = 1
    have h2 : (m + 1) % 9 = 1 := by
      have h_eq : (Nat.digits 10 (m + 1)).sum = 1 := by 
        omega 
      have h1 : (m + 1) % 9 = 1 := by
        have h_eq1 : (m + 1) % 9 = (Nat.digits 10 (m + 1)).sum % 9 := by
          rw [Nat.modEq_nine_digits_sum (m + 1)]
        rw [h_eq] at h_eq1 
        omega
      exact h1
    have h3 : (m + 1) % 9 = 6 := by
      omega 
    omega 
  constructor 
  · -- Show that 3 ∉ t
    intro h
    rw [ht] at h
    rcases h with ⟨m, hm1, hm2⟩
    rw [hS] at hm1
    rw [hS] at hm2
    have h1 : m % 9 = 5 := by
      have h_eq : (Nat.digits 10 m).sum = 1274 := hm1
      have h1 : m % 9 = 5 := by 
        have h_eq1 : m % 9 = (Nat.digits 10 m).sum % 9 := by
          rw [Nat.modEq_nine_digits_sum (m)]
        rw [h_eq] at h_eq1 
        omega 
      exact h1
    -- S(m+1) = 3
    have h2 : (m + 1) % 9 = 3 := by
      have h_eq : (Nat.digits 10 (m + 1)).sum = 3 := by 
        omega 
      have h1 : (m + 1) % 9 = 3 := by
        have h_eq1 : (m + 1) % 9 = (Nat.digits 10 (m + 1)).sum % 9 := by
          rw [Nat.modEq_nine_digits_sum (m + 1)]
        rw [h_eq] at h_eq1 
        omega
      exact h1
    have h3 : (m + 1) % 9 = 6 := by
      omega 
    omega 
  constructor
  · -- Show that 12 ∉ t
    intro h
    rw [ht] at h
    rcases h with ⟨m, hm1, hm2⟩
    rw [hS] at hm1
    rw [hS] at hm2
    have h1 : m % 9 = 5 := by
      have h_eq : (Nat.digits 10 m).sum = 1274 := hm1
      have h1 : m % 9 = 5 := by 
        have h_eq1 : m % 9 = (Nat.digits 10 m).sum % 9 := by
          rw [Nat.modEq_nine_digits_sum (m)]
        rw [h_eq] at h_eq1 
        omega 
      exact h1
    -- S(m+1) = 12
    have h2 : (m + 1) % 9 = 3 := by
      have h_eq : (Nat.digits 10 (m + 1)).sum = 12 := by
        omega 
      have h1 : (m + 1) % 9 = 3 := by 
        have h_eq1 : (m + 1) % 9 = (Nat.digits 10 (m + 1)).sum % 9 := by
          rw [Nat.modEq_nine_digits_sum (m + 1)]
        rw [h_eq] at h_eq1 
        omega
      exact h1
    have h3 : (m + 1) % 9 = 6 := by 
      omega 
    omega 
  · -- Show that 1265 ∉ t
    intro h
    rw [ht] at h
    rcases h with ⟨m, hm1, hm2⟩
    rw [hS] at hm1
    rw [hS] at hm2
    have h1 : m % 9 = 5 := by
      have h_eq : (Nat.digits 10 m).sum = 1274 := hm1
      have h1 : m % 9 = 5 := by 
        have h_eq1 : m % 9 = (Nat.digits 10 m).sum % 9 := by
          rw [Nat.modEq_nine_digits_sum (m)]
        rw [h_eq] at h_eq1 
        omega 
      exact h1
    -- S(m+1) = 1265
    have h2 : (m + 1) % 9 = 5 := by
      have h_eq : (Nat.digits 10 (m + 1)).sum = 1265 := by 
        omega 
      have h1 : (m + 1) % 9 = 5 := by 
        have h_eq1 : (m + 1) % 9 = (Nat.digits 10 (m + 1)).sum % 9 := by
          rw [Nat.modEq_nine_digits_sum (m + 1)]
        rw [h_eq] at h_eq1 
        omega 
      exact h1 
    have h3 : (m + 1) % 9 = 6 := by 
      omega 
    omega