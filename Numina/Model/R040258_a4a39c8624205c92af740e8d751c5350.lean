import Mathlib

theorem inequalities_284378 (n : ℕ) (h₀ : 2 ≤ n) (x : ℝ) (hx : |x| < 1) :
    (1 - x) ^ n + (1 + x) ^ n < 2 ^ n := by
  have h1 : -1 < x := by linarith [abs_lt.mp hx]
  have h2 : x < 1 := by linarith [abs_lt.mp hx]
  have h3 : (1 - x) > 0 := by linarith
  have h4 : (1 + x) > 0 := by linarith
  have h5 : (1 - x) < 2 := by linarith
  have h6 : (1 + x) < 2 := by linarith
  have h7 : x ^ 2 < 1 := by nlinarith [abs_lt.mp hx]

  have h8 : n ≥ 2 := by linarith

  have h9 : ∀ (k : ℕ), k ≥ 2 → (1 - x) ^ k + (1 + x) ^ k < (2 : ℝ) ^ k := by
    intro k hk
    have hk2 : k ≥ 2 := by linarith
    have base2 : (1 - x) ^ 2 + (1 + x) ^ 2 < (2 : ℝ) ^ 2 := by
      nlinarith [show (0 : ℝ) < 1 - x from by linarith, show (0 : ℝ) < 1 + x from by linarith, sq_nonneg (x ^ 2 - 1), h7]

    have step : ∀ (m : ℕ), m ≥ 2 → (1 - x) ^ m + (1 + x) ^ m < (2 : ℝ) ^ m →
        (1 - x) ^ (m + 1) + (1 + x) ^ (m + 1) < (2 : ℝ) ^ (m + 1) := by
      intro m hm h
      have h10 : (1 - x) ^ (m + 1) + (1 + x) ^ (m + 1) = (1 - x) * ((1 - x) ^ m) + (1 + x) * ((1 + x) ^ m) := by
        ring_nf
      rw [h10]
      have h11 : (1 - x) * ((1 - x) ^ m) + (1 + x) * ((1 + x) ^ m) < (2 : ℝ) ^ (m + 1) := by
        have h12 : (1 - x) * ((1 - x) ^ m) + (1 + x) * ((1 + x) ^ m) < (1 - x) * ((2 : ℝ) ^ m) + (1 + x) * ((2 : ℝ) ^ m) := by
          have h13 : (1 - x) ^ m < (2 : ℝ) ^ m := by
            have h14 : (1 - x) < (2 : ℝ) := by linarith
            have h15 : (1 - x) ^ m < (2 : ℝ) ^ m := by
              apply pow_lt_pow_left
              all_goals nlinarith
            linarith
          have h16 : (1 + x) ^ m < (2 : ℝ) ^ m := by
            have h17 : (1 + x) < (2 : ℝ) := by linarith
            have h18 : (1 + x) ^ m < (2 : ℝ) ^ m := by
              apply pow_lt_pow_left
              all_goals nlinarith
            linarith
          have h17 : (1 - x) > (0 : ℝ) := by linarith
          have h18 : (1 + x) > (0 : ℝ) := by linarith
          nlinarith
        have h13 : (1 - x) * ((2 : ℝ) ^ m) + (1 + x) * ((2 : ℝ) ^ m) = (2 : ℝ) ^ (m + 1) := by
          ring_nf
        nlinarith
      linarith
    exact Nat.le_induction base2 step k hk2
  specialize h9 n h8
  simpa using h9