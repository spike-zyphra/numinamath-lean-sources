import Mathlib

theorem number_theory_15482 {A B : ℕ} (hA : A = 111111) (hB : B = 142857) :
    ∃ N, N = 63 ∧ N > 0 ∧ (Nat.digits 10 N).length ≤ 6 ∧ N * (A * B) ≡ 1 [ZMOD 1000000] := by 
  use 63
  constructor
  · rfl
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num [Int.ModEq, hA, hB]