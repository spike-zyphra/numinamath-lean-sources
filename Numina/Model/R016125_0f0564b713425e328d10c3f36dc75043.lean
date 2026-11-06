import Mathlib

theorem algebra_112662 {u : ℕ → ℝ} (hu1 : u 1 = 1 / 2)
    (hsum : ∀ n ≥ 1, ∑ i in Finset.Icc 1 n, u i = n ^ 2 * u n) :
    ∀ n ≥ 1, u n = 1 / (n * (n + 1)) := by
  intro n hn 
  have h1 : ∀ n ≥ 1, u n = 1 / (n * (n + 1)) := by 
    intro n hn 
    induction' n using Nat.strongRecOn with n ih 
    cases n with 
    | zero => 
      exfalso 
      linarith 
    | succ n => 
      cases n with 
      | zero => 
        rw [hu1]
        norm_num 
      | succ n => 
        have eq1 := hsum (n + 1) (by linarith)
        have eq2 := hsum (n + 2) (by linarith)
        simp [Finset.sum_Icc_succ_top, ih (n + 1) (by linarith)] at eq1 eq2 
        field_simp at eq1 eq2 ⊢ 
        ring_nf at eq1 eq2 ⊢ 
        nlinarith 
  exact h1 n hn