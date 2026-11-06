import Mathlib

theorem number_theory_176332 (n : ℕ) (h₀ : n > 0) :
    (n^7 - n) % (n + n^2 + n^3) = 0 := by
  have h1 : n + n^2 + n^3 ∣ n^7 - n := by
    use n^4 - n^3 + n - 1
    cases n with
    | zero =>
      all_goals omega
    | succ n =>
      simp [Nat.pow_succ, Nat.mul_succ, Nat.pow_succ, Nat.mul_add]
      <;> ring_nf
      <;> omega
      all_goals omega
  exact Nat.dvd_iff_mod_eq_zero.mp h1