import Mathlib

theorem number_theory_101815 (p n : ℕ) (hp : Nat.Prime p) :
    p ∣ 3^(n + p) - 3^(n + 1) := by
  have h5 : ∀ (n : ℕ), p ∣ 3 ^ (n + p) - 3 ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      have h7 : p ∣ 3 ^ (0 + p) - 3 ^ (0 + 1) := by
        have eq3 : 3 ^ (0 + p) - 3 ^ (0 + 1) = (3 ^ p - 3) := by
          simp
        rw [eq3]
        have h50 : p ∣ 3 ^ p - 3 := by
          have h7 : 3 ^ p ≡ 3 [MOD p] := by
            have h10 : Fact p.Prime := ⟨hp⟩
            rw [← ZMod.eq_iff_modEq_nat p]
            simp [ZMod.pow_card]
          exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h7)
        exact h50
      exact h7
    | succ n ih =>
      have eq1 : 3 ^ (n + 1 + p) = 3 * (3 ^ (n + p)) := by
        ring_nf
      have eq2 : 3 ^ (n + 1 + 1) = 3 * (3 ^ (n + 1)) := by
        ring_nf
      have eq3 : 3 ^ (n + 1 + p) - 3 ^ (n + 1 + 1) = 3 * (3 ^ (n + p) - 3 ^ (n + 1)) := by
        rw [eq1, eq2]
        <;> omega
      have h8 : p ∣ 3 ^ (n + 1 + p) - 3 ^ (n + 1 + 1) := by
        rw [eq3]
        apply dvd_mul_of_dvd_right
        exact ih
      exact h8
  exact h5 n