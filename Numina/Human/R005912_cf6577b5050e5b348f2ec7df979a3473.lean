import Mathlib

-- define the function rk
def r (k: ℕ):= (Nat.choose 127 k) % 8

/-Let rk denote the remainder when
Nat.choose 127 k is divided by 8 . Compute r1+2r2+..63r63.-/

theorem combinatorics_610680: ∑ k ∈ Finset.Icc 1 63, k * r k = 8096 := by

  simp [r]
  native_decide
