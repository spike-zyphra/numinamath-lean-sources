import Mathlib

theorem algebra_292184 (a b : ℝ) (n : ℕ) (h₀ : 0 < n) (a_seq : ℕ → ℝ)
    (h₁ : a_seq 0 = a) (h₂ : a_seq n = b) :
    ∑ i ∈ Finset.range n, (a_seq (i + 1) - a_seq i) = b - a := by

  have h3 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (a_seq (i + 1) - a_seq i) = a_seq n - a_seq 0 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      all_goals simp [sub_add_cancel]
  have h4 : ∑ i ∈ Finset.range n, (a_seq (i + 1) - a_seq i) = a_seq n - a_seq 0 := by
    apply h3
  rw [h4]
  rw [h₂, h₁]
  all_goals linarith