import Mathlib

theorem number_theory_7515 (p : ℕ) [hp : Fact (Nat.Prime p)] (h : p ≡ 1 [MOD 4]) :
    ∃ x y : ℤ, x^2 - p * y^2 ≡ -1 [ZMOD 4] := by 
  use 0, 1
  simp [Int.ModEq, Nat.ModEq] at h ⊢
  omega