import Mathlib

theorem algebra_180310 (a : ℕ → ℝ) (ha : ∀ n, a n = a (n - 1) + 1) (ha0 : a 0 = 0)
    (h : ∑ i in Finset.range n, a i ≤ 11) :
    n ≤ 5 := by
  have h1 : ∀ (n : ℕ), a n = (n : ℝ) := by
    intro n 
    have h2 : ∀ (k : ℕ), a k = (k : ℝ) := by 
      intro k 
      induction' k using Nat.strongRecOn with k ih
      cases k with 
      | zero =>
        norm_num [ha0]
      | succ k =>
        have h3 : a (k + 1) = a k + 1 := by 
          specialize ha (k + 1)
          simpa using ha 
        rw [h3]
        rw [ih k (by linarith)]
        all_goals simp [add_comm]
        all_goals norm_num 
        all_goals ring 
    simpa using h2 n

  have h2 : ∑ i in Finset.range n, a i = (↑n * ((↑n : ℝ) - 1) / 2 : ℝ) := by 
    have h3 : ∀ (n : ℕ), ∑ i in Finset.range n, a i = (↑n * ((↑n : ℝ) - 1) / 2 : ℝ) := by 
      intro n 
      induction n with 
      | zero =>
        simp 
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        rw [h1 n]
        field_simp at *
        ring_nf 
    specialize h3 n 
    simpa using h3

  have h3 : n ≤ 5 := by
    by_contra h4
    push_neg at h4
    have h4' : n ≥ 6 := by omega
    have h7 : ∑ i in Finset.range n, a i > 11 := by
      rw [h2]
      have h8 : (↑n : ℝ) ≥ (6 : ℝ) := by exact_mod_cast (show n ≥ 6 by omega)
      nlinarith [sq_nonneg ((↑n : ℝ) - (6 : ℝ)), sq_nonneg ((↑n : ℝ) - (6 : ℝ))]
    linarith [h, h7]
  linarith