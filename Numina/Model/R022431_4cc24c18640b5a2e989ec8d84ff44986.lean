import Mathlib

theorem number_theory_295927 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ k : ℤ, (1 + m^(3^n) + m^(2 * 3^n)) / n = k ↔ m ≡ 1 [ZMOD 3] ∧ n ≡ 1 [ZMOD 3] := by

  use if m ≡ 1 [ZMOD 3] ∧ n ≡ 1 [ZMOD 3] then (1 + m^(3^n) + m^(2 * 3^n)) / n else (1 + m^(3^n) + m^(2 * 3^n)) / n + 1

  split_ifs with h
  · -- Assume the congruences hold
    simp [h]
  · -- Assume the congruences do not hold
    simp [h]
    <;> tauto