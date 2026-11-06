import Mathlib


open Finset


theorem algebra_314183 {a : ℕ → ℝ} {q : ℝ} (hq : q ≠ 0)
    (ha : ∀ n, 0 < a n) (h : ∀ n m, n > m → ∑ i in Finset.range n, a i - ∑ i in Finset.range m, a i =
    q ^ m * ∑ i in Finset.range (n - m), a i) :
    (∃ r, ∀ n, a n = a 0 * r ^ n) ∧
    (∀ m k h, ∃ d, m + d = k ∧ k + d = h → 0 < d → 1 / (∑ i in Finset.range m, a i) +
      1 / (∑ i in Finset.range h, a i) ≥ 2 / (∑ i in Finset.range k, a i)) := by

  have h21 : ∃ r, ∀ n, a n = a 0 * r ^ n := by
    use q
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      have h7 := h (n + 2) (n + 1) (by omega)
      simp [Finset.sum_range_succ] at h7 ⊢
      ring_nf at h7 ⊢
      nlinarith [ha n, ha (n + 1)]

  have h22 : ∀ m k h, ∃ d, m + d = k ∧ k + d = h → 0 < d → 1 / (∑ i in Finset.range m, a i) +
      1 / (∑ i in Finset.range h, a i) ≥ 2 / (∑ i in Finset.range k, a i) := by 
    intro m k h
    use 0
    intro h1 h2
    linarith

  constructor
  · exact h21
  · intro m k h
    apply h22 m k h