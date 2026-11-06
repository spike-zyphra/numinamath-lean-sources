import Mathlib

theorem number_theory_222241 (p : ℕ) (hp : Nat.Prime p) (a b : ℕ)
    (ha : a < p) (hb : b < p) (hab : a > 0 ∧ b > 0) :
    ¬p ∣ a * b := by
  have h1 : a > 0 := hab.1
  have h2 : b > 0 := hab.2
  by_contra h
  have h3 : p ∣ a * b := h
  have h4 : p ∣ a ∨ p ∣ b := (Nat.Prime.dvd_mul hp).mp h3
  rcases h4 with (h5 | h6)
  · -- Assume p divides a
    have h5 : p ∣ a := h5
    have h7 : a < p := ha
    have h8 : p > 1 := Nat.Prime.two_le hp
    have h9 : a > 0 := h1
    have h11 : a % p = 0 := by
      exact Nat.dvd_iff_mod_eq_zero.mp h5
    -- Now from `a % p = 0` and `a < p`, we can derive `a = 0`.
    -- Since `a % p = 0` and `a < p`.
    -- When a natural number `a` is less than `p`, then `a % p = a`.
    have h13 : a % p = a := by
      rw [Nat.mod_eq_of_lt]
      all_goals
        omega
    -- Now from `h11 : a % p = 0` and `h13 : a % p = a`, we have `a = 0`.
    have h12 : a = 0 := by
      omega
    -- This contradicts with `h1 : a > 0`.
    omega
  · -- Assume p divides b
    have h6 : p ∣ b := h6
    have h8 : p > 1 := Nat.Prime.two_le hp
    have h9 : b > 0 := h2
    have h11 : b % p = 0 := by
      exact Nat.dvd_iff_mod_eq_zero.mp h6
    have h10 : b < p := hb
    have h13 : b % p = b := by
      rw [Nat.mod_eq_of_lt]
      all_goals
        omega
    -- Now from `h11 : b % p = 0` and `h13 : b % p = b`, we have `b = 0`.
    have h12 : b = 0 := by
      omega
    -- This contradicts with `h2 : b > 0`.
    omega