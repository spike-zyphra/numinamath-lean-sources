import Mathlib

theorem algebra_223158 (a : ℕ → ℝ) (ha : ∀ k, 2 ≤ k → a (k - 1) = (3 * k ^ 2 - 3 * k + 1) / (k ^ 2 - k) ^ 3) :
    ∑ i in Finset.Icc 1 1985, a i = (1986 ^ 3 - 1) / 1986 ^ 3 := by

  have h1 : ∀ k : ℕ, 2 ≤ k → a (k - 1) = (1 / ((k - 1 : ℝ) ) ^ 3 - 1 / ((k : ℝ) ) ^ 3) := by
    intro k hk
    have eq2 : a (k - 1) = (3 * k ^ 2 - 3 * k + 1) / (k ^ 2 - k) ^ 3 := by
      apply ha k hk
    rw [eq2]
    field_simp [(show ((k : ℝ) ^ 2 - k) ≠ 0 by
      have hk1 : (k : ℝ) ≥ (2 : ℝ) := by exact_mod_cast hk
      nlinarith), (show ((k : ℝ) - 1) ≠ 0 by
        have hk1 : (k : ℝ) ≥ (2 : ℝ) := by exact_mod_cast hk
        nlinarith), (show (k : ℝ) ≠ 0 by
          have hk1 : (k : ℝ) ≥ (2 : ℝ) := by exact_mod_cast hk
          nlinarith)]
    <;> ring_nf 

  have h2 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, a i = (1 : ℝ) - 1 / ((n + 1 : ℝ) ^ 3) := by
    intro n 
    induction n with 
    | zero =>
      simp 
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      have h3 : a (n + 1) = (1 / ((↑n + 1 : ℝ)) ^ 3 - 1 / ((↑n + 2 : ℝ)) ^ 3) := by
        have eq1 : a (n + 1) = (3 * (n + 2 : ℕ) ^ 2 - 3 * (n + 2 : ℕ) + 1) / ((n + 2 : ℕ) ^ 2 - (n + 2 : ℕ)) ^ 3 := by
          specialize ha (n + 2) (by omega)
          simpa using ha
        rw [eq1]
        field_simp [(show ((n + 1 : ℝ) ) ≠ 0 by
          have : (n : ℝ) ≥ 0 := by simp
          linarith 
        ), (show ((n + 2 : ℝ) ) ≠ 0 by 
          have : (n : ℝ) ≥ 0 := by simp
          linarith 
        ), (show (( (n + 2 : ℝ) ) ^ 2 - (n + 2 : ℝ)) ≠ 0 by 
          have : (n : ℝ) ≥ 0 := by simp
          nlinarith 
        )
        ]
        <;> ring_nf 
      rw [h3]
      field_simp at *
      ring_nf

  specialize h2 1985
  norm_num at h2 ⊢ 
  <;> linarith