import Mathlib

theorem algebra_199680 {a : ℕ → ℝ} {h : ∃ d, ∀ n, a n = a 0 + d * n}
    (s : ℕ → ℝ) (hs : ∀ n, s n = ∑ i in Finset.range n, a i) :
    ∀ k, ∃ q, ∀ r ≤ k, 0 < r → (s (k + r) - s (k - r)) / r = q := by
  intro k
  rcases h with ⟨d, had⟩
  use 2 * a 0 + (2 * d * k - d)
  intro r hr h0r
  have h1 : s (k + r) = ((↑(k + r) : ℝ) / 2) * (2 * a 0 + ((↑(k + r) : ℝ) - 1) * d) := by
    rw [hs (k + r)]
    have h2 : ∀ n : ℕ, ∑ i in Finset.range n, a i = ((↑n : ℝ) / 2) * (2 * a 0 + (↑n - 1 : ℝ) * d) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp [had n]
        <;> ring_nf 
    specialize h2 (k + r)
    norm_num at h2 ⊢
    linarith
  have h2 : s (k - r) = ((↑(k - r) : ℝ) / 2) * (2 * a 0 + ((↑(k - r) : ℝ) - 1) * d) := by
    rw [hs (k - r)]
    have h3 : ∀ n : ℕ, ∑ i in Finset.range n, a i = ((↑n : ℝ) / 2) * (2 * a 0 + (↑n - 1 : ℝ) * d) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp [had n]
        <;> ring_nf 
    specialize h3 (k - r)
    norm_num at h3 ⊢
    linarith
  rw [h1, h2]
  field_simp at *
  ring_nf