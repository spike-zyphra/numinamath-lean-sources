import Mathlib

theorem algebra_206461 (d : ℕ → ℝ) (h₀ : d 0 = 5) (h₁ : ∀ n, d (n + 1) = d n + 7)
    (h₂ : ∑ i in Finset.range 30, d i = x) :
    x = 3195 := by

  have h3 : ∀ n, d n = 5 + 7 * (n : ℝ) := by
    intro n
    induction n with
    | zero =>
      simp [h₀]
      <;> norm_num
    | succ k ih =>
      have h4 : d (k + 1) = d k + 7 := h₁ k
      rw [h4]
      rw [ih]
      simp [add_mul, mul_add]
      <;> ring

  have h5 : ∑ i in Finset.range 30, d i = 3195 := by
    simp_rw [h3]
    norm_num [Finset.sum_range_succ]
    <;> ring

  linarith [h₂, h5]