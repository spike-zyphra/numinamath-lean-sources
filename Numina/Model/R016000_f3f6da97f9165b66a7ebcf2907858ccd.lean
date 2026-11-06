import Mathlib


theorem algebra_100100 (a : ℕ → ℝ) (h : ∀ m n, m ≥ n → 2 * (a (m + n) + a (m - n)) = a (2 * m) + a (2 * n))
    (ha : a 1 = 1) : ∀ n, a n = n ^ 2 := by

  have a00 : a 0 = (0 : ℝ) := by
    have h1 := h 0 0 (by norm_num)
    norm_num at h1 ⊢
    linarith

  intro n
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero =>
    simp [a00]
  | succ n =>
    cases n with
    | zero =>
      norm_num [ha]
    | succ n =>
      have eq3 : a 2 = (4 : ℝ) := by
        have h10 := h 1 0 (by norm_num)
        norm_num at h10 ⊢
        linarith [ha, a00]

      have eq4 : ∀ (k : ℕ), a (2 * k) = 4 * a k := by
        intro k
        have h0 := h k 0 (by linarith)
        simp at h0 ⊢
        linarith

      have eq6 : 2 * (a ((n + 1 + 1)) + a n) = a (2 * (n + 1)) + a 2 := by
        specialize h (n + 1) 1 (by
          omega
        )
        simpa using h

      have eq7 : a (2 * (n + 1)) = 4 * a (n + 1) := by
        specialize eq4 (n + 1)
        simpa using eq4

      have h8 : a n = (n : ℝ) ^ 2 := by
        specialize ih n (by linarith)
        simpa using ih

      have h9 : a (n + 1) = ((n + 1 : ℝ) ) ^ 2 := by
        specialize ih (n + 1) (by linarith)
        simpa using ih

      rw [eq7, eq3] at eq6
      rw [h8, h9] at eq6

      have h10 : a ((n + 1 + 1 : ℕ)) = ((n + 1 + 1 : ℝ) ) ^ 2 := by
        simp [show (n + 1 + 1 : ℕ) = n + 2 by omega] at *
        nlinarith

      simpa using h10