import Mathlib

theorem algebra_177644 {a : ℕ → ℝ} (ha1 : a 1 = 1) (ha2 : a 2 = 1 / 2)
    (han : ∀ n ≥ 2, a n * (a (n - 1) + a (n + 1)) = 2 * a (n + 1) * a (n - 1)) :
    a 2012 = 1 / 2012 := by 
  have h1 : ∀ (n : ℕ), a (n + 1) = 1 / ((n + 1 : ℝ)) := by
    intro n 
    induction' n using Nat.strongRecOn with n ih 
    cases n with 
    | zero =>
      norm_num [ha1]
    | succ n =>
      cases n with 
      | zero =>
        norm_num [ha2]
      | succ n =>
        have eq1 := han (n + 1 + 1) (by linarith)
        have eq2 := ih (n + 1) (by linarith)
        have eq3 := ih (n) (by linarith)
        simp [show n + 1 + 1 = n + 2 by omega] at eq1 
        simp [eq2, eq3] at eq1 
        field_simp at eq1 ⊢ 
        ring_nf at eq1 ⊢ 
        nlinarith 
  have h2 := h1 2011 
  norm_num at h2 ⊢ 
  linarith