import Mathlib

theorem number_theory_57725 (a : ℕ → ℕ) (ha : StrictMono a) (apos : ∀ n, 0 < a n)
    (ha1 : a 1 = 1) (han : ∀ n, a (n + 1) ≤ 2 * n) :
    ∀ n, 0 < n → ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ n = a p - a q := by
  have h1 := han 0
  norm_num at h1
  have h2 : 0 < a 1 := apos 1
  have h3 : a 1 = 1 := ha1
  linarith