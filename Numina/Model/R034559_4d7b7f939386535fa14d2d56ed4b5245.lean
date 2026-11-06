import Mathlib

theorem number_theory_246572 :
    (∀ n : ℕ, Odd n → ∃ k : ℕ, n = 2 * k + 1 → n ^ 2 ≡ 1 [MOD 8]) ∧
    ¬∃ m : ℕ, ∀ i ∈ Finset.range 45, ∃ j : ℕ, Odd j ∧ j = m + 2 * i ∧
      ∃ l : ℕ, ∑ i ∈ Finset.range 5, (j + 2 * i) ^ 2 = l ^ 2 ∧
      ∃ p : ℕ, ∑ i ∈ Finset.range 9, (j + 2 * i) ^ 2 = p ^ 2 := by
  constructor
  · -- Proof of a): ∀ n, if n is odd, then ∃ k : n = 2k+1 → n^2 ≡ 1 [MOD 8]
    intro n hn
    use (n - 1) / 2
    intro h_eq
    have h_eq_mod : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
      have h1 : n % 2 = 1 := by
        obtain ⟨k, hk⟩ := hn
        omega
      omega
    rcases h_eq_mod with (h | h | h | h)
    · -- n ≡ 1 [MOD 8]
      simp [Nat.ModEq, Nat.pow_mod, h]
      <;> omega
    · -- n ≡ 3 [MOD 8]
      simp [Nat.ModEq, Nat.pow_mod, h]
      <;> omega
    · -- n ≡ 5 [MOD 8]
      simp [Nat.ModEq, Nat.pow_mod, h]
      <;> omega
    · -- n ≡ 7 [MOD 8]
      simp [Nat.ModEq, Nat.pow_mod, h]
      <;> omega
  · -- Proof of b): ¬∃ m : ℕ, ∀ i ∈ Finset.range 45, ∃ j : ℕ, Odd j ∧ j = m + 2 * i ∧
    rintro ⟨m, hm⟩
    have h0 := hm 0 (by simp)
    rcases h0 with ⟨j0, h_j0_odd, hj0, l0, hsum0, p0, hsum0'⟩
    have h_eq1 : ∑ i in Finset.range 5, (j0 + 2 * i) ^ 2 = l0 ^ 2 := by
      simpa using hsum0
    have h_eq3 : j0 % 2 = 1 := by
      obtain ⟨k, hk⟩ := h_j0_odd
      omega
    have h_eq4 : j0 % 8 = 1 ∨ j0 % 8 = 3 ∨ j0 % 8 = 5 ∨ j0 % 8 = 7 := by
      have h1 : j0 % 2 = 1 := h_eq3
      omega
    have h_eq5 : (∑ i in Finset.range 5, (j0 + 2 * i) ^ 2) % 8 = 5 := by
      have h1 : j0 % 8 = 1 ∨ j0 % 8 = 3 ∨ j0 % 8 = 5 ∨ j0 % 8 = 7 := h_eq4
      rcases h1 with (h1 | h1 | h1 | h1)
      · -- j0 ≡ 1 [MOD 8]
        simp [Finset.sum_range_succ, Nat.add_mod, Nat.mul_mod, pow_two, Nat.pow_mod, h1] at *
        all_goals omega
      · -- j0 ≡ 3 [MOD 8]
        simp [Finset.sum_range_succ, Nat.add_mod, Nat.mul_mod, pow_two, Nat.pow_mod, h1] at *
        all_goals omega
      · -- j0 ≡ 5 [MOD 8]
        simp [Finset.sum_range_succ, Nat.add_mod, Nat.mul_mod, pow_two, Nat.pow_mod, h1] at *
        all_goals omega
      · -- j0 ≡ 7 [MOD 8]
        simp [Finset.sum_range_succ, Nat.add_mod, Nat.mul_mod, pow_two, Nat.pow_mod, h1] at *
        all_goals omega
    have h_eq6 : l0 ^ 2 % 8 = 0 ∨ l0 ^ 2 % 8 = 1 ∨ l0 ^ 2 % 8 = 4 := by
      have h1 : l0 % 8 = 0 ∨ l0 % 8 = 1 ∨ l0 % 8 = 2 ∨ l0 % 8 = 3 ∨ l0 % 8 = 4 ∨ l0 % 8 = 5 ∨ l0 % 8 = 6 ∨ l0 % 8 = 7 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
      all_goals omega
    have h_eq7 : (∑ i in Finset.range 5, (j0 + 2 * i) ^ 2) % 8 = l0 ^ 2 % 8 := by
      omega
    omega