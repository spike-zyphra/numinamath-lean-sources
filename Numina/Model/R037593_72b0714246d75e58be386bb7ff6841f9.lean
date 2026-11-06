import Mathlib

open Real

theorem algebra_601133 {a : ℕ → ℝ} (ha1 : a 1 = 1)
    (han : ∀ n > 0, a (n + 1) = (1 + 2 * a n) / (1 + a n)) :
    ∀ n > 0, a n < (1 + sqrt 5) / 2 := by
  intro n hn
  have hn' : n ≥ 1 := by linarith
  have h2 : ∀ n ≥ 1, a n < (1 + sqrt 5) / 2 := by
    intro n hn
    induction n with
    | zero =>
      exfalso
      linarith
    | succ n ih =>
      cases n with
      | zero =>
        rw [ha1]
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      | succ n =>
        have hn' : n ≥ 0 := by linarith
        have h3 := ih (by linarith)
        have pos_val : ∀ k ≥ 1, a k > 0 := by
          intro k hk
          induction k with
          | zero =>
            exfalso
            linarith
          | succ k ihk =>
            cases k with
            | zero =>
              rw [ha1]
              norm_num
            | succ k =>
              have h_pos_val := ihk (by linarith)
              rw [han (k + 1) (by linarith)]
              apply div_pos
              linarith
              linarith
        have hn1 : a (n + 1) > 0 := pos_val (n + 1) (by linarith)
        rw [han (n + 1) (by linarith)]
        apply (div_lt_iff (by linarith)).mpr
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg (a (n + 1) - (1 + Real.sqrt 5) / 2), sq_nonneg (a (n + 1) + 1), Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by linarith), sq_nonneg (a (n + 1) - (1 + sqrt 5) / 2)]
  specialize h2 n hn'
  linarith