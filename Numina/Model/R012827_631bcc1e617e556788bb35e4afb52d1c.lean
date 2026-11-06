import Mathlib

theorem number_theory_272456 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : b > a) :
    ¬(Nat.factorial b - Nat.factorial a ≡ 7 [MOD 10]) := by
  by_contra h1
  have h2 : (Nat.factorial b - Nat.factorial a) % 10 = 7 := by
    norm_num [Nat.ModEq] at h1
    omega
  have h3 : b ≥ a + 1 := by omega
  by_cases h4 : a ≤ 4
  · -- if a ≤ 4, then compute directly.
    have h5 : a ≤ 4 := h4
    have h8 : a ≥ 1 := by linarith
    have h9 : Nat.factorial a % 10 = 1 ∨ Nat.factorial a % 10 = 2 ∨ Nat.factorial a % 10 = 6 ∨ Nat.factorial a % 10 = 4 := by
      interval_cases a <;> try { simp [Nat.factorial] }
      <;> omega
    by_cases h10 : b ≤ 4
    · -- if b ≤ 4, compute directly.
      interval_cases b <;> interval_cases a
      <;> norm_num [Nat.factorial] at h2 h9 ⊢
      <;> omega
    · -- if b > 4
      have h11 : b ≥ 5 := by omega
      have h12 : Nat.factorial b % 10 = 0 := by
        have h11' : b ≥ 5 := h11
        have h13 : 5 ∣ Nat.factorial b := by
          apply Nat.dvd_factorial
          all_goals omega
        have h14 : 2 ∣ Nat.factorial b := by
          apply Nat.dvd_factorial
          all_goals omega
        omega
      omega
  · -- case a > 4
    have h13 : a ≥ 5 := by omega
    have h14 : Nat.factorial a % 10 = 0 := by
      have h13' : a ≥ 5 := h13
      have h11' : 5 ∣ Nat.factorial a := by
        apply Nat.dvd_factorial
        all_goals omega
      have h12' : 2 ∣ Nat.factorial a := by
        apply Nat.dvd_factorial
        all_goals omega
      omega
    have h15 : b ≥ 6 := by
      omega
    have h16 : b ≥ 5 := by omega
    have h17 : Nat.factorial b % 10 = 0 := by
      have h18 : b ≥ 5 := h16
      have h18' : 5 ∣ Nat.factorial b := by
        apply Nat.dvd_factorial
        all_goals omega
      have h18'' : 2 ∣ Nat.factorial b := by
        apply Nat.dvd_factorial
        all_goals omega
      omega
    omega