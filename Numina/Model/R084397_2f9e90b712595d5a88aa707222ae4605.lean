import Mathlib

theorem number_theory_15809 (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a % 5 = 1 ∧ b % 5 = 2 ∧ c % 5 = 3) :
    (a * b * c) % 5 = 1 := by
  rcases h with ⟨ha1, hb2, hc3⟩
  simp [Nat.mul_mod, ha1, hb2, hc3]