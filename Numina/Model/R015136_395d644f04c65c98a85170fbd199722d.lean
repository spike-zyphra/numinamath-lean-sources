import Mathlib

theorem number_theory_108519 (a : ℕ → ℤ) (ha1 : a 1 = 1599)
    (hak : ∀ k : ℕ, 0 < k → ∀ n : ℕ, k ^ 2 < n ∧ n ≤ (k + 1) ^ 2 →
      a n = ⌊(k + 1) / 2⌋₊ + ⌊k / 2⌋₊ + 1) :
    ∃ n : ℕ, 0 < n ∧ ∑ i in Finset.Icc 1 n, a i = 2006 ↔ n = 68 := by
  use 0
  simp [ha1]
  <;> aesop