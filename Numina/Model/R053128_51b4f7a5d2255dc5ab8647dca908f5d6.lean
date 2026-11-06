import Mathlib

theorem number_theory_227546 {p : ℕ} (hp : Nat.Prime p) (h : p - 1 > 0) :
    ∃ k, (10 ^ (p - 1) + 1) * k ≡ 0 [MOD p] := by
  use 0
  simp [Nat.ModEq]