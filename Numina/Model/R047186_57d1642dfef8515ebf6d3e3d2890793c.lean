import Mathlib

theorem number_theory_94886 : IsGreatest {x | ∀ n : ℕ, Even n → x ∣ (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9)} 15 := by
  constructor
  · -- Show 15 is in the set
    intro n hn
    have h1 : n % 2 = 0 := by
      obtain ⟨k, hk⟩ := hn
      omega
    have h2 : (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9) % 3 = 0 := by
      have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h3 with (h | h | h)
      · -- If n % 3 = 0
        simp [h, Nat.mul_mod, Nat.add_mod]
        <;> omega
      · -- If n % 3 = 1
        simp [h, Nat.mul_mod, Nat.add_mod]
        <;> omega
      · -- If n % 3 = 2
        simp [h, Nat.mul_mod, Nat.add_mod]
        <;> omega
    have h3 : (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9) % 5 = 0 := by
      have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
      rcases h4 with (h | h | h | h | h)
      · -- If n % 5 = 0
        simp [h, Nat.mul_mod, Nat.add_mod]
        <;> omega
      · -- If n % 5 = 1
        simp [h, Nat.mul_mod, Nat.add_mod]
        <;> omega
      · -- If n % 5 = 2
        simp [h, Nat.mul_mod, Nat.add_mod]
        <;> omega
      · -- If n % 5 = 3
        simp [h, Nat.mul_mod, Nat.add_mod]
        <;> omega
      · -- If n % 5 = 4
        simp [h, Nat.mul_mod, Nat.add_mod]
        <;> omega
    have h4 : 15 ∣ (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9) := by
      omega
    exact h4
  · -- Show 15 is greatest in the set
    intro x hx
    have h1 := hx 0 (by decide)
    have h2 := hx 2 (by decide)
    have h3 := hx 8 (by decide)
    have h4 := hx 16 (by decide)
    norm_num at h1 h2 h3 h4
    have h5 : x ∣ 15 := by
      exact Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3) h4
    have h6 : x ≤ 15 := by
      exact Nat.le_of_dvd (by norm_num) h5
    linarith