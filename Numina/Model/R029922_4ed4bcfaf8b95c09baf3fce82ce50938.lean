import Mathlib

theorem number_theory_4858 :
    ∀ {p : ℕ}, 0 < p → (Nat.totient p = p - 1 ↔ Nat.Prime p) := by
  intro p hp
  have h1 : p > 0 := hp
  have h4 : Nat.totient p = p - 1 ↔ Nat.Prime p := by
    have h5 : p ≥ 1 := by linarith
    rw [Nat.totient_eq_iff_prime h5]
  assumption