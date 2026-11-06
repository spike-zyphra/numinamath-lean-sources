import Mathlib

def a (n : ℕ) : ℤ := 2^(3*n) + 3^(6*n+2) + 5^(6*n+2)

theorem number_theory_139954 : IsGreatest {x | ∀ i ∈ Finset.range 2000, x ∣ a i} 7 := by
  constructor
  · -- Show 7 is in the set
    show ∀ i ∈ Finset.range 2000, 7 ∣ a i
    intro i hi
    have h1 : i < 2000 := by
      simp at hi ⊢
      omega
    have h2 : (7 : ℤ) ∣ a i := by
      have h1 : (a i) % 7 = 0 := by
        simp [a]
        have h1 : ∀ (n : ℕ), (2 : ℤ) ^ (3 * n) % 7 = 1 := by
          intro n
          induction n with
          | zero => norm_num
          | succ n ih =>
            simp [pow_succ, pow_mul] at ih ⊢
            omega
        have h2 : ∀ (n : ℕ), (3 : ℤ) ^ (6 * n + 2) % 7 = 2 := by
          intro n
          induction n with
          | zero => norm_num
          | succ n ih =>
            simp [pow_succ, pow_mul] at ih ⊢
            omega
        have h3 : ∀ (n : ℕ), (5 : ℤ) ^ (6 * n + 2) % 7 = 4 := by
          intro n
          induction n with
          | zero => norm_num
          | succ n ih =>
            simp [pow_succ, pow_mul] at ih ⊢
            omega
        have h1' : (2 : ℤ) ^ (3 * i) % 7 = 1 := h1 i
        have h2' : (3 : ℤ) ^ (6 * i + 2) % 7 = 2 := h2 i
        have h3' : (5 : ℤ) ^ (6 * i + 2) % 7 = 4 := h3 i
        omega
      exact Int.dvd_of_emod_eq_zero h1
    exact h2
  · -- Show 7 is greatest in the set
    intro x hx
    have h : ∀ i ∈ Finset.range 2000, x ∣ a i := hx
    have h1 := h 0 (by simp)
    have h2 := h 1 (by simp)
    norm_num [a] at h1 h2
    have h3 : x ∣ 7 := by
      exact Int.dvd_gcd h1 h2
    have h4 : x ≤ 7 := by
      exact Int.le_of_dvd (by norm_num) h3
    linarith