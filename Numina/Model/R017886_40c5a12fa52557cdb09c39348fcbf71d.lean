import Mathlib

theorem number_theory_185555 (n : ℕ) (hn : Odd n ∧ n > 1) :
    ∃ i, i ∈ Finset.Icc 1 (n - 1) ∧ n ∣ (2 ^ i - 1) := by 
  have h11 : n > 1 := hn.right
  have h7 : n % 2 = 1 := by 
    rcases hn with ⟨hn_odd, hn_gt⟩
    obtain ⟨k, hk⟩ := hn_odd
    omega 
  have h2 : Nat.Coprime 2 n := by 
    have : n % 2 = 1 := h7 
    have h5 : n > 0 := by omega
    have h6 : Nat.gcd 2 n = 1 := by
      have h8 : n % 2 = 1 := h7 
      simp [Nat.gcd_comm]
      <;> try { 
        have h9 : (n : ℕ) % 2 = 1 := by omega 
        have : n > 1 := h11
        omega 
      }
      <;> try { 
        tauto 
      }
    rw [Nat.coprime_iff_gcd_eq_one] 
    exact h6 
  have h10 : 2 ^ (n.totient) ≡ (1 : ℕ) [MOD n] := Nat.ModEq.pow_totient h2
  have h18 : n ∣ (2 ^ (n.totient) - 1) := by
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h10)
  use (n.totient)
  constructor 
  · -- Show i ∈ Finset.Icc 1 (n - 1)
    rw [Finset.mem_Icc]
    constructor
    · -- Show 1 ≤ n.totient
      have h11 : n > 1 := hn.right 
      have h36 : 1 ≤ n.totient := by 
        have h13 : n > 1 := h11
        have h17 : n.totient > 0 := by 
          apply Nat.totient_pos.mpr
          linarith 
        linarith 
      exact h36 
    · -- Show n.totient ≤ n - 1
      have h11 : n > 1 := hn.right 
      have h38 : n.totient ≤ n - 1 := by 
        have h13 : n > 1 := h11
        have h18 : n.totient < n := by
          apply Nat.totient_lt
          all_goals try { linarith } 
          all_goals try { linarith }
        omega 
      exact h38 
  · -- Show n ∣ (2 ^ (n.totient) - 1)
    exact h18