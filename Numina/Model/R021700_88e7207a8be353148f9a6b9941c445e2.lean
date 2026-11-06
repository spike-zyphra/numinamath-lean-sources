import Mathlib

theorem algebra_125415 {a b : ℕ → ℝ} {A B : ℕ → ℝ}
    (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ d, ∀ n, b n = b 0 + d * n)
    (hA : ∀ n, A n = ∑ i in Finset.range n, a i)
    (hB : ∀ n, B n = ∑ i in Finset.range n, b i)
    (h : ∀ n, A n / B n = (2 * n - 1) / (3 * n + 1)) :
    ∀ n, a n / b n = (4 * n - 3) / (6 * n - 2) := by
  have h1 := h 0
  simp [hA, hB] at h1
  all_goals
    norm_num at h1 ⊢
    <;> try { linarith }
    <;> try { tauto }