import Mathlib

open Real

theorem algebra_134445 (a : ℕ → ℝ) (ha : a 0 = 0)
    (h : ∀ n, a (n + 1) = a n + 1 / (n + 1) - 1 / (n + 2)) :
    a 44 = 44 / 45 := by

  have eq5 : ∀ n : ℕ, a n = 1 - 1 / (↑n + 1 : ℝ) := by
    intro n
    induction n with
    | zero =>
      rw [ha]
      norm_num
    | succ n ih =>
      have eq5 : a (n + 1) = a n + 1 / (↑n + 1 : ℝ) - 1 / (↑n + 2 : ℝ) := by
        specialize h n
        simpa using h
      rw [eq5]
      rw [ih]
      field_simp at *
      <;> ring_nf <;> field_simp
  have eq544 : a 44 = 1 - 1 / (↑(44 : ℕ) + 1 : ℝ) := by
    apply eq5 44
  rw [eq544]
  norm_num