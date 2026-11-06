import Mathlib

theorem algebra_13044 (a : ℕ → ℤ) (ha1 : a 1 = 20) (ha2 : a 2 = 17)
    (han : ∀ n > 0, a (n + 2) = 2 * a (n + 1) - a n) :
    a 2017 = -6028 := by
  have h1 : ∀ n : ℕ, a (n + 1) = -3 * (n + 1) + 23 := by
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
        have h3 := ih n (by linarith)
        have h4 := ih (n + 1) (by linarith)
        have h5 : a ((n + 2) + 1) = 2 * a ((n + 1) + 1) - a (n + 1) := by 
          specialize han (n + 1) (by linarith)
          simpa using han
        simp [show n + 2 + 1 = n + 3 by omega, show n + 1 + 1 = n + 2 by omega] at h4 h5 ⊢
        linarith
  have h2 : a 2017 = -3 * 2017 + 23 := by 
    specialize h1 2016 
    norm_num at h1 ⊢ 
    linarith
  rw [h2]
  norm_num