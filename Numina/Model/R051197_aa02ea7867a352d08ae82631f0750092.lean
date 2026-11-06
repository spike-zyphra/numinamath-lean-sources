import Mathlib

theorem algebra_300339 : Set.Infinite {(k, b) : ℤ × ℤ | ∃! x : ℝ, x^2 = k * x + b} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (2 * (n : ℤ), -(n : ℤ) ^ 2))
  · -- Show that f is injective
    intro n m
    simp [Prod.ext_iff] at *
    <;> omega
  · -- Show that ∀ n, f(n) ∈ {(k, b) : ℤ × ℤ | ∃! x : ℝ, x^2 = k * x + b}
    intro n
    simp [Prod.ext_iff]
    use (n : ℝ)
    constructor
    · -- Show that (n : ℝ) is a solution
      simp
      <;> ring_nf
      <;> norm_num
      <;> ring
    · -- Show that (n : ℝ) is a unique solution
      intro y hy
      have h_eq : (y : ℝ) ^ 2 = (2 * (n : ℤ) : ℝ) * y + (- (n : ℤ) ^ 2 : ℝ) := by
        simpa using hy
      have h : (y - (n : ℝ)) ^ 2 = 0 := by
        nlinarith [sq_nonneg (y - (n : ℝ)), sq_nonneg (y - (n : ℝ))]
      have h_zero : (y - (n : ℝ)) = 0 := by
        rw [sq_eq_zero_iff] at h
        exact h
      have h_eq_n : y = (n : ℝ) := by
        linarith [h_zero]
      linarith [h_eq_n]