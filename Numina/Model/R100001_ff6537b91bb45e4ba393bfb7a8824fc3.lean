import Mathlib

theorem number_theory_240592 (n : ℕ) (h₀ : Odd n) :
    ∃ m, n = m^2 - (m-1)^2 := by
  obtain ⟨k, hk⟩ := h₀
  use k + 1
  cases k with 
  | zero =>
    simp [hk]
    <;> ring_nf <;> omega 
  | succ k =>
    simp [pow_two, Nat.succ_eq_add_one, Nat.add_comm, Nat.mul_add, hk]
    <;> ring_nf <;> omega