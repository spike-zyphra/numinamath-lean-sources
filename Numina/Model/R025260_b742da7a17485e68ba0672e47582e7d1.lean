import Mathlib

theorem algebra_290065 (x : ℝ) (h : ∑ i ∈ Finset.range 999, x / (i + 1) / (i + 2) = 999) :
    x = 1000 := by
  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.range n, x / (i + 1) / (i + 2) = x * (1 - 1 / (n + 1 : ℝ)) := by
    intro n
    induction n with
    | zero =>
      simp
      <;> ring
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp at *
      <;> ring_nf
      <;> field_simp at *
      <;> ring
  have h2 := h1 999
  rw [h2] at h
  norm_num at h
  linarith