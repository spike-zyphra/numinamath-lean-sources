import Mathlib

theorem algebra_2433 {n : ℕ} (hn : n > 0) (a b : ℚ) (h : a + 1 / b = 0) :
    a ^ (2 * n + 1) + (1 / b) ^ (2 * n + 1) = 0 := by
  by_cases h1 : b = 0
  · -- Case b = 0.
    have h2 : a = 0 := by
      rw [h1] at h
      norm_num at h ⊢
      all_goals linarith
    rw [h2, h1]
    norm_num
    <;> ring_nf <;> norm_num
    all_goals try { tauto }
  · -- Case b ≠ 0.
    have h3 : a = -1 / b := by
      field_simp [h1] at h ⊢
      all_goals linarith
    rw [h3]
    have h4 : ((-1 / b) : ℚ) ^ (2 * n + 1) + (1 / b) ^ (2 * n + 1) = 0 := by
      have h5 : ((-1 / b) : ℚ) ^ (2 * n + 1) = - ((1 / b) ^ (2 * n + 1)) := by
        have h6 : ∀ k : ℕ, ((-1 / b) : ℚ) ^ (2 * k + 1) = - ((1 / b) ^ (2 * k + 1)) := by
          intro k
          induction k with
          | zero =>
            simp
            <;> ring_nf <;> field_simp [h1]
          | succ k ih =>
            simp [pow_succ, pow_mul] at ih ⊢
            ring_nf at ih ⊢
            <;> try { 
              rw [mul_comm]
              <;> ring_nf <;> field_simp [h1]
            }
            all_goals try { 
              tauto
            }
            all_goals try { 
              linarith [ih]
            }
            all_goals try { 
              tauto 
            }
        specialize h6 n
        simpa using h6
      rw [h5]
      <;> ring_nf
    exact h4