import Mathlib

theorem algebra_52329 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 2)
    (hsum : ∀ n ≥ 1, ∑ i in Finset.Icc 1 n, a i = n ^ 2 * a n) :
    ∀ n ≥ 1, a n = 1 / (n * (n + 1)) := by 
  intro n hn
  induction n with 
  | zero => 
    exfalso 
    linarith
  | succ n ih =>
    cases n with
    | zero => 
      norm_num at ih ⊢
      all_goals 
        rw [ha1]
        all_goals 
          norm_num
    | succ n => 
      have eq1 := hsum (n + 1) (by linarith)
      have eq2 := hsum (n + 2) (by linarith)
      rw [Finset.sum_Icc_succ_top (by linarith)] at eq2
      simp [ih] at eq1 eq2 ⊢ 
      field_simp at eq1 eq2 ⊢ 
      ring_nf at eq1 eq2 ⊢ 
      <;> nlinarith 
      all_goals 
        nlinarith