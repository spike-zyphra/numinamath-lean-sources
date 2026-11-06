import Mathlib

theorem algebra_161156 (a : ℕ → ℝ) (ha0 : a 0 = 2) (han : ∀ n, a (n + 1) = a n / (1 + a n)) :
    a 2012 = 2 / 4025 := by
  have h1 : ∀ n : ℕ, a n = 2 / (2 * (n : ℝ) + 1) := by
    intro n 
    induction n with
    | zero =>
      simp [ha0]
      all_goals norm_num
    | succ n ih =>
      have eq1 : a (n + 1) = a n / (1 + a n) := han n
      rw [eq1]
      rw [ih]
      field_simp
      ring_nf
      all_goals norm_num
      <;> ring
  specialize h1 2012
  norm_num at h1 ⊢ 
  linarith [h1]