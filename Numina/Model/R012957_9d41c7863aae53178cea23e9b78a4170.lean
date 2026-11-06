import Mathlib

theorem number_theory_175098 (n : ℕ) (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : ∃ m, m^2 = n + (10 * (n % 10) + n / 10)) :
    n = 29 ∨ n = 38 ∨ n = 47 ∨ n = 56 ∨ n = 65 ∨ n = 74 ∨ n = 83 ∨ n = 92 := by
  rcases h₂ with ⟨m, hm⟩
  have h5 : m ^ 2 = n + (10 * (n % 10) + n / 10) := hm
  have h6 : m ≤ 14 := by
    by_contra h
    push_neg at h
    have h7 : m ≥ 15 := by
      omega
    have h8 : m ^ 2 ≥ 225 := by
      have h9 : m ≥ 15 := by
        omega
      have h10 : m ^ 2 ≥ 225 := by
        nlinarith [h9]
      linarith
    have h9 : m ^ 2 ≤ 198 := by
      have h10 : m ^ 2 = n + (10 * (n % 10) + n / 10) := hm
      rw [h10] at *
      have h11 : n < 100 := h₀
      have h12 : n > 9 := h₁
      have h13 : n ≤ 99 := by 
        omega
      have h14 : n + (10 * (n % 10) + n / 10) ≤ 198 := by
        interval_cases n <;> norm_num
        all_goals omega
      linarith
    linarith
  have h8 : m ^ 2 % 11 = 0 := by
    have eq : m ^ 2 = 11 * ((n / 10) + (n % 10)) := by 
      omega
    omega
  have hm_is_mul_of_11 : m % 11 = 0 := by 
    by_contra h
    push_neg at h
    have h4 : m % 11 = 1 ∨ m % 11 = 2 ∨ m % 11 = 3 ∨ m % 11 = 4 ∨ m % 11 = 5 ∨ m % 11 = 6 ∨ m % 11 = 7 ∨ m % 11 = 8 ∨ m % 11 = 9 ∨ m % 11 = 10 := by
      omega
    rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> simp [Nat.pow_mod, h4, Nat.mul_mod, Nat.add_mod] at h8 <;> omega
  have h_m_eq_11 : m = 11 := by 
    have : m = 0 ∨ m = 11 := by
      omega
    rcases this with (h | h)
    · -- m = 0
      have h_zero_sub : m = 0 := h
      rw [h_zero_sub] at hm
      have : n + (10 * (n % 10) + n / 10) = 0 := by
        nlinarith
      have h10 : n + (10 * (n % 10) + n / 10) ≥ 20 := by
        have h10 : n ≥ 10 := by
          omega
        have h11 : n < 100 := h₀
        interval_cases n <;> omega <;> try { norm_num }
        all_goals 
          omega
      omega
    · -- m = 11
      exact h
  rw [h_m_eq_11] at hm
  have h12 : n + (10 * (n % 10) + n / 10) = 121 := by
    nlinarith
  have : n = 29 ∨ n = 38 ∨ n = 47 ∨ n = 56 ∨ n = 65 ∨ n = 74 ∨ n = 83 ∨ n = 92 := by
    have h10 : n ≥ 10 := by
      omega
    have h11 : n < 100 := h₀
    interval_cases n <;> norm_num at *
    <;> try { tauto }
    all_goals try { omega }
  assumption