import Mathlib

theorem algebra_307429 {a : ℕ → ℝ}
    (ha1 : a 1 = 1) (ha2 : a 2 = 1 / 2)
    (han : ∀ n ≥ 2, a n * (a (n - 1) + a (n + 1)) = 2 * a (n + 1) * a (n - 1)) :
    a 2012 = 1 / 2012 := by

  have a_eq (n : ℕ) : a (n + 1) = 1 / (n + 1 : ℝ) := by
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      norm_num
      all_goals
        norm_num [ha1]
    | succ n =>
      cases n with
      | zero =>
        norm_num
        all_goals
          norm_num [ha2]
      | succ n =>
        have h1 := ih (n) (by linarith)
        have h2 := ih (n + 1) (by linarith)
        have h3 := han (n + 2) (by linarith)
        simp [show n + 2 - 1 = n + 1 by omega, show n + 2 + 1 = n + 3 by omega] at h3
        simp [h1, h2] at h3
        field_simp at h3 ⊢
        ring_nf at h3 ⊢
        nlinarith
  have ha2012 : a 2012 = 1 / (2012 : ℝ) := by
    specialize a_eq 2011
    norm_num at a_eq ⊢
    linarith
  simpa using ha2012