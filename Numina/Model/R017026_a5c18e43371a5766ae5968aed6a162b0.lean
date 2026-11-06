import Mathlib

theorem algebra_272590 {a b : ℕ → ℤ} (ha1 : a 1 = -1) (hb1 : b 1 = 2)
    (han : ∀ n > 0, a (n + 1) = -b n ∧ b (n + 1) = 2 * a n - 3 * b n) :
    b 2015 + b 2016 = -3 * 2 ^ 2015 := by

  have h1 : ∀ n : ℕ, b (n + 1) = 4 * (-1 : ℤ) ^ (n + 1) - 3 * (-2 : ℤ) ^ (n + 1) := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      norm_num [hb1]
    | succ n =>
      cases n with
      | zero =>
        have h2 := han 1 (by norm_num)
        have h3 : b 2 = 2 * a 1 - 3 * b 1 := h2.2
        rw [ha1, hb1] at h3
        norm_num at h3 ⊢
        all_goals linarith 
      | succ n =>
        have eq1 := ih (n) (by linarith)
        have eq2 := ih (n + 1) (by linarith)
        have h3 := han (n + 1) (by linarith)
        have h4 := han (n + 2) (by linarith)
        simp [show n + 1 + 1 = n + 2 by omega, show n + 2 + 1 = n + 3 by omega] at h3 h4 ⊢
        rw [show b (n + 3) = 2 * a (n + 2) - 3 * b (n + 2) by tauto]
        -- need to show a (n+2) = -b (n+1)
        have eq3 : a (n + 2) = -b (n + 1) := by 
          have h5 := (han (n + 1) (by linarith)).1
          simpa using h5
        rw [eq3]
        simp [eq1, eq2] at *
        ring_nf 
  have h2 : b 2015 = 4 * (-1) ^ 2015 - 3 * (-2) ^ 2015 := by
    specialize h1 2014
    simpa using h1
  have h3 : b 2016 = 4 * (-1) ^ 2016 - 3 * (-2) ^ 2016 := by
    specialize h1 2015
    simpa using h1
  rw [h2, h3]
  norm_num