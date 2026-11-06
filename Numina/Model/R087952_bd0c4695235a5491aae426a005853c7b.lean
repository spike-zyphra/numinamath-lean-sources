import Mathlib

theorem algebra_313032 (a : ℕ → ℝ) (ha : ∀ n, a n = n ^ 2 + 2 * n - 3) :
    ∑ i in Finset.Icc 1 n, a i = (1 / 3) * n ^ 3 + (3 / 2) * n ^ 2 - (11 / 6) * n := by
  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, a i = (1 / 3) * n ^ 3 + (3 / 2) * n ^ 2 - (11 / 6) * n := by 
    intro n
    induction n with 
    | zero =>
      simp [Finset.sum_eq_zero]
      <;> norm_num [ha]
      <;> try { linarith }
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num)]
      rw [ih]
      simp [ha]
      all_goals ring_nf <;> field_simp <;> ring
      <;> try { linarith }
  simpa using h1 n