import Mathlib

theorem number_theory_42734 (n : ℕ) (hn : 1 ≤ n) :
    ∃ k, ∀ i, 2^(2^i) ≡ 2^(2^(i + k)) [ZMOD n] := by
  use 0
  intro i
  simp [Int.ModEq]