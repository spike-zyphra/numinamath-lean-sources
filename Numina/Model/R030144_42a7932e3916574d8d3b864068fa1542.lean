import Mathlib

theorem algebra_137930 {x : ℝ} (hx : 4 * x ^ 2 - 5 * ⌊x⌋ + 8 * (x - ⌊x⌋) = 19) :
    x = 5 / 2 := by
  let n := ⌊x⌋
  have hn1 : (n : ℝ) ≤ x := by exact Int.floor_le x
  have hn2 : x < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
  have eq1 : 4 * x ^ 2 + 8 * x - 13 * (n : ℝ) = 19 := by
    have eq2 : 4 * x ^ 2 - 5 * (n : ℝ) + 8 * (x - (n : ℝ)) = 19 := by
      simpa using hx
    nlinarith
  have h3 : n ≤ 2 := by
    by_contra h
    push_neg at h
    have hn4 : (n : ℝ) ≥ 3 := by exact_mod_cast (h : n ≥ 3)
    nlinarith [sq_nonneg (x - 2 : ℝ), sq_nonneg ((n : ℝ) - 3 : ℝ), sq_nonneg (x - (n : ℝ) : ℝ)]
  have h4 : n ≥ -1 := by
    by_contra h
    push_neg at h
    have hn5 : n ≤ -2 := by omega
    have hn6 : (n : ℝ) ≤ -2 := by exact_mod_cast (hn5 : n ≤ -2)
    nlinarith [sq_nonneg (x + 1 : ℝ), sq_nonneg ((n : ℝ) + 2 : ℝ), sq_nonneg (x - (n : ℝ) : ℝ)]
  have h5 : n = -1 ∨ n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases h5 with h5 | h5 | h5 | h5
  · -- case n = -1
    have hn7 : (n : ℝ) = -1 := by exact_mod_cast (h5 : n = -1)
    rw [hn7] at eq1
    nlinarith [sq_nonneg (x + 0.58 : ℝ), sq_nonneg (x - 0.58 : ℝ), sq_nonneg (x + 1 : ℝ), sq_nonneg (x - (n : ℝ) : ℝ)]
  · -- case n = 0
    have hn7 : (n : ℝ) = 0 := by exact_mod_cast (h5 : n = 0)
    rw [hn7] at eq1
    nlinarith [sq_nonneg (x - 1.398 : ℝ), sq_nonneg (x + 1.398 : ℝ), sq_nonneg (x - 0 : ℝ), sq_nonneg (x - (n : ℝ) : ℝ)]
  · -- case n = 1
    have hn7 : (n : ℝ) = 1 := by exact_mod_cast (h5 : n = 1)
    rw [hn7] at eq1
    nlinarith [sq_nonneg (x - 2 : ℝ), sq_nonneg (x + 4 : ℝ), sq_nonneg (x - 0 : ℝ), sq_nonneg (x - (n : ℝ) : ℝ)]
  · -- case n = 2
    have hn7 : (n : ℝ) = 2 := by exact_mod_cast (h5 : n = 2)
    rw [hn7] at eq1
    nlinarith [sq_nonneg (x - 2.5 : ℝ), sq_nonneg (x + 4.5 : ℝ), sq_nonneg (x - 0 : ℝ), sq_nonneg (x - (n : ℝ) : ℝ)]