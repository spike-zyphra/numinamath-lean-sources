import Mathlib

theorem number_theory_288442 {a b : ℕ → ℤ}
    (ha1 : a 1 = 1) (hb1 : b 1 = 0)
    (han : ∀ n ≥ 1, a (n + 1) = 7 * a n + 12 * b n + 6)
    (hbn : ∀ n ≥ 1, b (n + 1) = 4 * a n + 7 * b n + 3) :
    ∀ n ≥ 1, ∃ x, a n ^ 2 = x ^ 3 - (x - 1) ^ 3 := by
  intro n hn
  have h1 : ∀ n ≥ 1, a n ^ 2 = (b n + 1) ^ 3 - (b n) ^ 3 := by
    intro n hn
    induction n with
    | zero =>
      exfalso
      exact Nat.lt_irrefl 0 hn
    | succ n ih =>
      cases n with
      | zero =>
        rw [ha1, hb1]
        norm_num
      | succ n =>
        have h2 := ih (Nat.succ_le_of_lt (Nat.succ_pos n))
        have ha2 := han (n + 1) (by linarith)
        simp [show n + 1 + 1 = n + 2 by omega] at ha2
        have hb2 := hbn (n + 1) (by linarith)
        simp [show n + 1 + 1 = n + 2 by omega] at hb2
        simp [ha2, hb2] at *
        nlinarith [h2, sq_nonneg (a n), sq_nonneg (b n), sq_nonneg (a n - 1), sq_nonneg (b n - 1)]
  specialize h1 n hn
  use b n + 1
  linarith [h1]