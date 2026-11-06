import Mathlib


theorem algebra_217146 {f : ℕ → ℝ} (h : ∀ m n, m ≤ n → f (n + m) + f (n - m) = f (3 * n)) :
    ∀ n, f n = 0 := by

  have h1 : f 0 = 0 := by
    have h2 := h 0 0 (by norm_num)
    simp at h2
    linarith

  have h2 : f 1 = 0 := by
    have eq1 := h 1 1 (by norm_num)
    norm_num at eq1
    have eq2 := h 0 1 (by norm_num)
    norm_num at eq2
    have eq3 := h 1 2 (by norm_num)
    norm_num at eq3
    have eq4 := h 0 2 (by norm_num)
    norm_num at eq4
    linarith [h1]

  intro n
  have h5 : ∀ (n : ℕ), f n = 0 := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      exact h1
    | succ n =>
      cases n with
      | zero =>
        exact h2
      | succ n =>
        have eq1 := ih n (by omega)
        have eq2 := ih (n + 1) (by omega)
        have h_eq1 := h 1 (n + 1) (by omega)
        have h_eq2 := h 0 (n + 1) (by omega)
        simp [show n + 1 + 1 = n + 2 by omega, show (n + 1) - 1 = n by omega] at h_eq1
        simp [show n + 1 + 0 = n + 1 by omega, show (n + 1) - 0 = n + 1 by omega] at h_eq2
        have eq3 : f (n + 2) = 0 := by
          nlinarith [h_eq1, h_eq2, eq1, eq2]
        simpa using eq3

  specialize h5 n
  simpa using h5