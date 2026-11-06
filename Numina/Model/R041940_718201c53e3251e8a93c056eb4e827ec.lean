import Mathlib

theorem algebra_9063 {a : ℕ → ℝ} (ha1 : a 1 = 9 / 4)
    (han : ∀ n ≥ 1, 2 * a (n + 1) * a n - 7 * a (n + 1) - 3 * a n + 12 = 0)
    (c : ℕ → ℝ) (hc : ∀ n, c n = a n - 2) :
    ∀ n ≥ 1, c n = 1 / (3 ^ n + 1) := by
  intro n hn
  have h1 : ∀ n : ℕ, n ≥ 1 → c n = 1 / (3 ^ n + 1) := by
    intro n hn
    induction' n with n ih
    · linarith
    · cases n with
      | zero =>
        rw [hc 1]
        rw [ha1]
        norm_num
      | succ n =>
        have h2 := ih (by linarith)
        have eq1 := han (n + 1) (by linarith)
        have eq2 := han (n + 2) (by linarith)
        have eq3 : c (n + 1) = 1 / (3 ^ (n + 1) + 1) := by
          simpa using h2
        have eq4 : a (n + 1) = c (n + 1) + 2 := by linarith [hc (n + 1)]
        have eq5 : a (n + 2) = c (n + 2) + 2 := by linarith [hc (n + 2)]
        rw [eq4, eq5] at eq1
        rw [show c (n + 1) = 1 / (3 ^ (n + 1) + 1) by linarith [h2]] at eq1
        have eq7 : 2 * (c (n + 2) + 2) * (1 / (3 ^ (n + 1) + 1) + 2) - 7 * (c (n + 2) + 2) - 3 * (1 / (3 ^ (n + 1) + 1) + 2) + 12 = 0 := by
          nlinarith
        have eq8 : c (n + 2) = 1 / (3 ^ (n + 2) + 1) := by
          field_simp at eq7 ⊢
          ring_nf at eq7 ⊢
          nlinarith [sq_pos_of_pos (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3)]
        simpa using eq8
  specialize h1 n hn
  simpa using h1