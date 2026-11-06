import Mathlib
open Real

theorem algebra_8077 (d : ℕ → ℝ) (h₀ : d 0 = 5) (h₁ : ∀ n, d (n + 1) = d n + 1 / 4) :
    IsLeast {n | ∑ i in Finset.range n, d i > 1000} 73 := by
  have h2 : ∀ n, d n = 5 + (n : ℝ) / 4 := by
    intro n
    induction n with
    | zero =>
      rw [h₀]
      all_goals norm_num
    | succ n ih =>
      have h : d (n + 1) = d n + 1 / 4 := h₁ n
      rw [h, ih]
      field_simp at *
      ring
  constructor
  · -- Show that 73 is in the set
    show ∑ i in Finset.range 73, d i > 1000
    have h3 : ∀ i : ℕ, d i = 5 + (i : ℝ) / 4 := h2
    rw [Finset.sum_congr rfl (fun i _ => h3 i)]
    norm_num [Finset.sum_range_succ]
  · -- Show that no smaller natural number is in the set
    intro n hn
    show n ≥ 73
    have h4 : ∑ i in Finset.range n, d i > 1000 := by
      simpa using hn
    by_contra h
    push_neg at h
    have h5 : n ≤ 72 := by linarith
    have h6 : ∑ i in Finset.range n, d i ≤ 1000 := by
      have h3 : ∀ i : ℕ, d i = 5 + (i : ℝ) / 4 := h2
      rw [Finset.sum_congr rfl (fun i _ => h3 i)]
      interval_cases n <;> norm_num [Finset.sum_range_succ]
    linarith