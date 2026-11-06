import Mathlib

theorem inequalities_5122 (x : ℕ → ℝ)
  (hx0 : x 0 = 2)
  (hxn : ∀ n, x (n + 1) = (x n ^ 4 + 1) / (5 * x n)) :
  ∀ n, n ≥ 1 → 1 / 5 ≤ x n ∧ x n < 2 := by
  intro n hn
  have h1 : ∀ (n : ℕ), n ≥ 1 → 1 / 5 ≤ x n ∧ x n < 2 := by
    intro n hn
    induction n with
    | zero => 
      exfalso
      linarith
    | succ n ih =>
      cases n with
      | zero =>
        constructor
        · -- Show 1/5 ≤ x 1
          have hx1 : x 1 = (x 0 ^ 4 + 1) / (5 * x 0) := hxn 0
          rw [hx1, hx0]
          norm_num
        · -- Show x 1 < 2
          have hx1 : x 1 = (x 0 ^ 4 + 1) / (5 * x 0) := hxn 0
          rw [hx1, hx0]
          norm_num
      | succ n =>
        have h4 := ih (by linarith)
        rcases h4 with ⟨h11, h12⟩
        have h2 : x (n + 2) = (x (n + 1) ^ 4 + 1) / (5 * x (n + 1)) := by
          specialize hxn (n + 1)
          simpa using hxn
        constructor
        · -- Show 1/5 ≤ x (n + 2)
          rw [h2]
          have h3 : 0 < x (n + 1) := by
            nlinarith
          have h5 : x (n + 1) ^ 4 - x (n + 1) + 1 ≥ 0 := by
            nlinarith [sq_nonneg (x (n + 1) ^ 2 - 1 / 2), sq_nonneg (x (n + 1) - 1), sq_nonneg (x (n + 1) ^ 2 - x (n + 1)), sq_nonneg (x (n + 1) - 1 / 2),
              pow_two_nonneg (x (n + 1) ^ 2 - 1), pow_two_nonneg (x (n + 1) - 1)]
          apply (le_div_iff₀ (by positivity)).mpr
          nlinarith [h5, mul_pos (show (0 : ℝ) < 5 by norm_num) (show 0 < x (n + 1) by nlinarith)]
        · -- Show x (n + 2) < 2
          rw [h2]
          have h3 : 0 < x (n + 1) := by
            nlinarith
          have h5 : x (n + 1) ^ 4 - 10 * x (n + 1) + 1 < 0 := by
            nlinarith [sq_nonneg (x (n + 1) ^ 2 - 2 * x (n + 1)), sq_nonneg (x (n + 1) - 1), sq_nonneg (x (n + 1) ^ 2 - 2),
                sq_nonneg (x (n + 1) ^ 2 - x (n + 1)), sq_nonneg (x (n + 1) - 1), sq_nonneg (x (n + 1) - 1 / 2),
                pow_two_nonneg (x (n + 1) ^ 2 - 2), pow_two_nonneg (x (n + 1) - 1)]
          apply (div_lt_iff₀ (by positivity)).mpr
          nlinarith [h5, mul_pos (show (0 : ℝ) < 5 by norm_num) (show 0 < x (n + 1) by nlinarith)]
  specialize h1 n hn
  simpa using h1