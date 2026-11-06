import Mathlib


theorem inequalities_282783 (x : ℝ) (hx : |x| < 1) (n : ℕ) (hn : 2 ≤ n) :
    (1 - x)^n + (1 + x)^n < 2^n := by
  have h1 : -1 < x := by
    linarith [abs_lt.mp hx]
  have h2 : x < 1 := by
    linarith [abs_lt.mp hx]

  have h3 : (1 - x) > 0 := by
    nlinarith
  have h4 : (1 + x) > 0 := by
    nlinarith

  have h5 : (1 - x) ^ n + (1 + x) ^ n < (2 : ℝ) ^ n := by
    have h6 : ∀ (k : ℕ), (1 - x) ^ (k + 2) + (1 + x) ^ (k + 2) < (2 : ℝ) ^ (k + 2) := by
      intro k
      induction k with
      | zero =>
        have h10 : (1 - x) ^ 2 + (1 + x) ^ 2 < (2 : ℝ) ^ 2 := by
          have h7 : (1 - x) ^ 2 + (1 + x) ^ 2 = 2 + 2 * x ^ 2 := by
            ring_nf
          have h8 : x ^ 2 < 1 := by
            nlinarith
          have h9 : (2 : ℝ) ^ 2 = 4 := by norm_num
          nlinarith [h7, h8, h9]
        simpa using h10
      | succ k ih =>
        have h10 : (1 - x) ^ (k + 1 + 2) + (1 + x) ^ (k + 1 + 2) < (2 : ℝ) ^ (k + 1 + 2) := by
          have eq1 : (1 - x) ^ (k + 1 + 2) + (1 + x) ^ (k + 1 + 2) = (1 - x) * ((1 - x) ^ (k + 2)) + (1 + x) * ((1 + x) ^ (k + 2)) := by
            ring_nf
          rw [eq1]
          have eq2 : (2 : ℝ) ^ (k + 1 + 2) = (2 : ℝ) ^ (k + 2) * 2 := by
            ring_nf
          have eq3 : (1 - x) * ((1 - x) ^ (k + 2)) + (1 + x) * ((1 + x) ^ (k + 2)) < (2 : ℝ) ^ (k + 2) * 2 := by
            have h9 : (1 - x) ^ (k + 2) > 0 := by positivity
            have h10 : (1 + x) ^ (k + 2) > 0 := by positivity
            nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg ((1 - x) ^ (k + 2) - (1 + x) ^ (k + 2)), sq_nonneg (x), sq_nonneg ((1 - x)), sq_nonneg ((1 + x)), mul_pos (show 0 < (1 - x : ℝ) by nlinarith) (show 0 < (1 + x : ℝ) by nlinarith), ih]
          nlinarith [eq2, eq3]
        simpa using h10
    have eq7 : n ≥ 2 := by omega
    have eq8 : n - 2 + 2 = n := by omega
    specialize h6 (n - 2)
    rw [eq8] at h6
    simpa using h6
  linarith