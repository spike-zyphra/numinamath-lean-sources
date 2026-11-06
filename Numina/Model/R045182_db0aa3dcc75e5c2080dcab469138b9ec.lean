import Mathlib

theorem algebra_253423 {a : ℕ → ℝ} {S : ℕ → ℝ}
    (sdef : ∀ n, S n = ∑ i in Finset.Ico 1 (n+1), a i)
    (ha1 : a 1 = 2) (hsum : ∀ n, (n ^ 2 + 1) * a (n + 1) = (2 * n + 1) * S n + n ^ 4 + 2 * n ^ 3 + 3 * n ^ 2 + 2 * n + 2) :
    ∀ n≥1, a n = 3 * n ^ 2 - 3 * n + 2 ∧ S n = n * (n ^ 2 + 1) := by
  intro n hn
  have h1 : ∀ n : ℕ, n ≥ 1 → a n = 3 * (n : ℝ) ^ 2 - 3 * (n : ℝ) + 2 ∧ S n = (n : ℝ) * ((n : ℝ) ^ 2 + 1) := by
    intro n hn
    induction n with
    | zero => 
      exfalso
      linarith
    | succ n ih =>
      cases n with 
      | zero => 
        constructor 
        · -- Show that a 1 = 3 * 1 ^ 2 - 3 * 1 + 2
          norm_num [ha1]
          all_goals linarith
        · -- Show that S 1 = 1 * (1 ^ 2 + 1)
          have hS1 : S 1 = a 1 := by 
            rw [sdef 1]
            norm_num [Finset.sum_Ico_succ_top, ha1]
            all_goals linarith
          rw [hS1, ha1]
          norm_num 
          all_goals linarith
      | succ n => 
        have h2 := ih (by linarith)
        have eq1 := hsum (n + 1)
        have eq2 := hsum (n + 2)
        have hS1 : S (n + 1) = (n + 1 : ℝ) * ((n + 1 : ℝ) ^ 2 + 1) := by
          have h3 := h2.right
          norm_num at h3 ⊢
          nlinarith 
        -- Prove the value of a_{n + 2}
        have ha2 : a (n + 2) = 3 * ((n + 2 : ℝ) ) ^ 2 - 3 * ((n + 2 : ℝ) ) + 2 := by
          simp [show n + 1 + 1 = n + 2 by omega] at eq1 
          simp [hS1] at eq1 
          ring_nf at eq1 ⊢ 
          <;> nlinarith [sq_pos_of_pos (show ((n + 1 : ℝ) ) > 0 by positivity), sq_nonneg ((n + 1 : ℝ) ^ 2), sq_nonneg ((n + 2 : ℝ) ^ 2), sq_nonneg ((n : ℝ) ^ 2)]
        -- Prove the value of S_{n + 2}
        have hS2 : S (n + 2) = (n + 2 : ℝ) * ((n + 2 : ℝ) ^ 2 + 1) := by
          have eq3 : S (n + 2) = S (n + 1) + a (n + 2) := by 
            rw [sdef (n + 2), sdef (n + 1)]
            simp [Finset.sum_Ico_succ_top, mul_add, add_mul]
            <;> ring_nf <;> norm_num 
            all_goals try linarith 
          rw [eq3]
          rw [hS1, ha2]
          ring_nf 
          <;> norm_num 
          all_goals try nlinarith
        constructor 
        · -- Show the formula for a
          exact_mod_cast ha2 
        · -- Show the formula for S
          exact_mod_cast hS2 
  specialize h1 n hn
  norm_num at h1 ⊢
  tauto