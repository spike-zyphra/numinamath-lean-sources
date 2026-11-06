import Mathlib

theorem number_theory_76863 {a b : ℕ → ℤ}
    (ha1 : a 1 = 1) (hb1 : b 1 = 0)
    (han : ∀ n ≥ 1, a (n + 1) = 7 * a n + 12 * b n + 6)
    (hbn : ∀ n ≥ 1, b (n + 1) = 4 * a n + 7 * b n + 3) :
    ∀ n ≥ 1, ∃ m, a n ^ 2 = (m + 1) ^ 3 - m ^ 3 := by 
  intro n hn 
  have h2 : ∀ n ≥ 1, a n ^ 2 = (b n + 1) ^ 3 - (b n) ^ 3 := by 
    intro n hn 
    induction n with 
    | zero => 
      exfalso 
      linarith 
    | succ n ih => 
      cases n with 
      | zero => 
        rw [ha1, hb1] 
        all_goals norm_num 
      | succ n => 
        have eq1 : a (n + 2) = 7 * a (n + 1) + 12 * b (n + 1) + 6 := by 
          specialize han (n + 1) (by linarith) 
          simpa using han 
        have eq2 : b (n + 2) = 4 * a (n + 1) + 7 * b (n + 1) + 3 := by 
          specialize hbn (n + 1) (by linarith) 
          simpa using hbn 
        simp [eq1, eq2] at ih ⊢ 
        all_goals 
          ring_nf at ih ⊢ 
          <;> nlinarith [hbn 1 (by norm_num), han 1 (by norm_num), sq_nonneg (a 1 - b 1), sq_nonneg (a (n + 1) - b (n + 1)), sq_nonneg (a (n + 1) + b (n + 1))]
  
  specialize h2 n hn 
  refine ⟨b n, by linarith [h2]⟩