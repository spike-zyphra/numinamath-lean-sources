import Mathlib

theorem algebra_129784 (m n : ℕ) :
    ∑ k in Finset.range n, (m + k) * (m + k + 1) =
    (n / 3 : ℚ) * (3 * m ^ 2 + 3 * m * n + n ^ 2 - 1) := by
  have h1 : ∀ (n : ℕ), ∑ k in Finset.range n, (m + k) * (m + k + 1 : ℚ) =
    (n / 3 : ℚ) * (3 * m ^ 2 + 3 * m * n + n ^ 2 - 1) := by
    intro n 
    induction n with
    | zero =>
      norm_num 
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp at *
      ring_nf 
      <;> field_simp at *
      <;> ring
  specialize h1 n 
  norm_num at h1 ⊢ 
  <;> linarith