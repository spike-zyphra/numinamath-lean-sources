import Mathlib

theorem algebra_195690 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 2)
    (han : ∀ n ≥ 1, ∑ i in Finset.Icc 1 n, a i = n ^ 2 * a n) :
    ∀ n ≥ 1, a n = 1 / (n * (n + 1)) := by
  intro n hn
  have h1 : ∀ n ≥ 1, a n = 1 / (n * (n + 1)) := by
    intro n hn
    induction n with
    | zero => 
      exfalso
      linarith 
    | succ n ih => 
      cases n with 
      | zero => 
        rw [ha1]
        norm_num 
      | succ n => 
        have eq1 := han 1 (by norm_num)
        norm_num [Finset.sum_Icc_succ_top] at eq1 
        have eq2 := han (n + 2) (by linarith)
        have eq3 := han (n + 1) (by linarith)
        rw [show n + 2 = (n + 1) + 1 by omega] at eq2
        simp [Finset.sum_Icc_succ_top, ih (by linarith)] at eq2 eq3 
        field_simp at eq2 eq3 ⊢ 
        ring_nf at eq2 eq3 ⊢ 
        <;> nlinarith
  specialize h1 n hn
  simpa using h1