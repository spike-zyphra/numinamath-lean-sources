import Mathlib

theorem number_theory_172036 (p m : ℕ) (hp : p.Prime) (hm : m > 0) :
    p^3 + m * (p + 2) = m^2 + p + 1 ↔ (p, m) = (2, 5) := by
  constructor
  · -- Assume p^3 + m * (p + 2) = m^2 + p + 1, prove (p, m) = (2, 5)
    intro h_eq
    have eq1 : p ^ 3 + m * (p + 2) = m ^ 2 + p + 1 := h_eq
    by_cases h2 : p > 2
    · -- p > 2, so p must be odd
      have eq5 : p % 2 = 1 := by
        by_contra h
        push_neg at h
        have h1 : p % 2 = 0 := by
          omega
        have h7 : p > 2 := h2
        have h8 : ¬p.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by linarith) (by linarith)
        tauto
      have eq6 : (p ^ 3 + m * (p + 2) : ℕ) % 2 = (m ^ 2 + p + 1 : ℕ) % 2 := by
        omega
      have eq7 : (p : ℕ) % 2 = 1 := eq5
      have eq8 : (m ^ 2 + p + 1 : ℕ) % 2 = (m : ℕ) % 2 := by 
        have h7 : (p : ℕ) % 2 = 1 := eq7
        have h8 : (m ^ 2 : ℕ) % 2 = (m : ℕ) % 2 := by
          have h9 : m % 2 = 0 ∨ m % 2 = 1 := by omega
          rcases h9 with (h9 | h9)
          · -- m is even
            simp [Nat.add_mod, Nat.mul_mod, h9, Nat.pow_mod]
            <;> omega
          · -- m is odd
            simp [Nat.add_mod, Nat.mul_mod, h9, Nat.pow_mod]
            <;> omega
        omega
      have eq9 : (p ^ 3 + m * (p + 2) : ℕ) % 2 = (1 + (m : ℕ) % 2) % 2 := by
        have h7 : (p : ℕ) % 2 = 1 := eq7
        have h8 : (p + 2 : ℕ) % 2 = 1 := by
          omega
        have h9 : (p ^ 3 : ℕ) % 2 = 1 := by
          simp [Nat.pow_mod, h7]
          <;> omega
        have h10 : (m * (p + 2) : ℕ) % 2 = (m : ℕ) % 2 := by
          simp [Nat.mul_mod, h8]
          <;> omega
        omega
      omega
    · -- p ≤ 2, so p = 2
      have eq11 : p = 2 := by
        interval_cases p <;> norm_num at hp <;> omega
      rw [eq11] at eq1
      have eq32 : m = 5 := by
        nlinarith
      simp [eq11, eq32]
      all_goals tauto
  · -- Assume (p, m) = (2, 5), prove p^3 + m * (p + 2) = m^2 + p + 1
    rintro ⟨rfl, rfl⟩
    norm_num
    all_goals tauto