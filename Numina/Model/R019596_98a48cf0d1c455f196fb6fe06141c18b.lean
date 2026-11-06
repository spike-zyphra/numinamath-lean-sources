import Mathlib

theorem algebra_166542 {a : ℕ → ℝ} (ha1 : a 1 = 5)
    (han : ∀ n ≥ 1, a (n + 1) = (a n ^ 2 + 8 * a n + 16) / (4 * a n)) :
    ∀ n ≥ 1, a n ≥ 4 := by
  have h2 : ∀ n ≥ 1, a n ≥ 4 := by
    intro n hn
    have h3 : ∀ k : ℕ, a (k + 1) ≥ 4 := by
      intro k 
      induction k with
      | zero => 
        rw [ha1]
        norm_num
      | succ k ih => 
        have eq1 : a ((k + 1) + 1) = (a (k + 1) ^ 2 + 8 * a (k + 1) + 16) / (4 * a (k + 1)) := by 
          specialize han (k + 1) (by omega)
          simpa using han
        have eq2 : a (k + 1 + 1) ≥ 4 := by
          rw [eq1]
          have h4' : a (k + 1) ≥ 4 := by linarith [ih]
          have h5 : a (k + 1) > 0 := by linarith [h4']
          have h6 : (a (k + 1) ^ 2 + 8 * a (k + 1) + 16) / (4 * a (k + 1)) ≥ 4 := by
            apply (le_div_iff₀ (by positivity)).mpr 
            nlinarith [sq_nonneg (a (k + 1) - 4), sq_nonneg (a (k + 1)), h4']
          linarith
        simpa using eq2
    have eq3 : a n ≥ 4 := by
      specialize h3 (n - 1) 
      have h8 : n - 1 + 1 = n := by 
        omega 
      rw [h8] at h3
      linarith 
    linarith 
  intro n hn 
  specialize h2 n hn 
  linarith