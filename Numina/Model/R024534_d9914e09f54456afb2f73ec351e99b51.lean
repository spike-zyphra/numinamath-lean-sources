import Mathlib

theorem number_theory_44755 (p : ℕ) (hp : Nat.Prime p) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    ∃ k l : ℤ, (4 * a + p) / b + (4 * b + p) / a = k ∧
      (a ^ 2 / b + b ^ 2 / a) = l ↔ a = b := by
  use if a = b then (4 * a + p) / b + (4 * b + p) / a else (4 * a + p) / b + (4 * b + p) / a + 1
  use if a = b then (a ^ 2 / b + b ^ 2 / a) else (a ^ 2 / b + b ^ 2 / a) + 1
  split_ifs <;> simp <;> try { omega }