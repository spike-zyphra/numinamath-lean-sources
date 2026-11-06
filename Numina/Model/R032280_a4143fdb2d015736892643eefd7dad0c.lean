import Mathlib

theorem algebra_267294 (x : ℝ) (hx : x^2 - 8 * ⌊x⌋ + 7 = 0) :
    x = 1 ∨ x = Real.sqrt 33 ∨ x = Real.sqrt 41 ∨ x = 7 := by
  let n := ⌊x⌋
  have h1 : (n : ℝ) ≤ x := by exact Int.floor_le x
  have h2 : x < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
  have h3 : (x : ℝ)^2 = 8 * (n : ℝ) - 7 := by linarith
  have h4 : n ≥ 1 := by
    by_contra h
    push_neg at h
    have hn : n ≤ 0 := by omega
    have hn0 : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hn
    nlinarith [sq_nonneg (x - (n : ℝ)), sq_nonneg (x + (n : ℝ)), sq_nonneg (x ^ 2 - 8 * (n : ℝ) + 7)]
  have h5 : n ≤ 7 := by
    by_contra h
    push_neg at h
    have hn8 : n ≥ 8 := by omega
    have hn8' : (n : ℝ) ≥ (8 : ℝ) := by exact_mod_cast hn8
    nlinarith [sq_nonneg (x - (n : ℝ)), sq_nonneg (x + (n : ℝ)), sq_nonneg (x ^ 2 - 8 * (n : ℝ) + 7)]
  have hn1 : n ≤ 7 := by omega
  have hn2 : n ≥ 1 := by omega
  have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases this with h | h | h | h | h | h | h
  · -- Case n = 1
    have hn1 : (n : ℝ) = 1 := by exact_mod_cast h
    have hx1 : x^2 = 1 := by
      rw [hn1] at h3
      nlinarith
    have h8 : x ≥ 0 := by nlinarith
    have h9 : x ≤ 2 := by nlinarith
    have hx4 : x = 1 := by
      nlinarith [sq_nonneg (x - 1)]
    simp [hx4]
  · -- Case n = 2
    exfalso
    have hn2 : (n : ℝ) = 2 := by exact_mod_cast h
    rw [hn2] at h3
    have h8 : x ≥ 2 := by nlinarith
    have h9 : x < 3 := by nlinarith
    nlinarith [sq_nonneg (x - 3), sq_nonneg (x ^ 2 - 9)]
  · -- Case n = 3
    exfalso
    have hn3 : (n : ℝ) = 3 := by exact_mod_cast h
    rw [hn3] at h3
    have h8 : x ≥ 3 := by nlinarith
    have h9 : x < 4 := by nlinarith
    nlinarith [sq_nonneg (x - 3), sq_nonneg (x ^ 2 - 9)]
  · -- Case n = 4
    exfalso
    have hn4 : (n : ℝ) = 4 := by exact_mod_cast h
    rw [hn4] at h3
    have h8 : x ≥ 4 := by nlinarith
    have h9 : x < 5 := by nlinarith
    nlinarith [sq_nonneg (x - 4), sq_nonneg (x ^ 2 - 16)]
  · -- Case n = 5
    have hn5 : (n : ℝ) = 5 := by exact_mod_cast h
    have hx1 : x^2 = 33 := by
      rw [hn5] at h3
      nlinarith
    have h8 : x ≥ 5 := by nlinarith
    have h9 : x < 6 := by nlinarith
    have hx33 : x = Real.sqrt 33 := by
      have hx33 : x ≥ 0 := by nlinarith
      have hx33' : x ^ 2 = 33 := by linarith
      have hx33 : x = Real.sqrt 33 := by
        rw [← hx33']
        field_simp
      exact hx33
    simp [hx33]
    <;> nlinarith [Real.sqrt_nonneg 33, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 33)]
  · -- Case n = 6
    have hn6 : (n : ℝ) = 6 := by exact_mod_cast h
    have hx1 : x^2 = 41 := by
      rw [hn6] at h3
      nlinarith
    have h8 : x ≥ 6 := by nlinarith
    have h9 : x < 7 := by nlinarith
    have hx41 : x = Real.sqrt 41 := by
      have hx41 : x ≥ 0 := by nlinarith
      have hx41' : x ^ 2 = 41 := by linarith
      have hx41 : x = Real.sqrt 41 := by
        rw [← hx41']
        field_simp
      exact hx41
    simp [hx41]
    <;> nlinarith [Real.sqrt_nonneg 41, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)]
  · -- Case n = 7
    have hn7 : (n : ℝ) = 7 := by exact_mod_cast h
    have hx1 : x^2 = 49 := by
      rw [hn7] at h3
      nlinarith
    have h8 : x ≥ 7 := by nlinarith
    have h9 : x < 8 := by nlinarith
    have hx7 : x = 7 := by
      nlinarith [sq_nonneg (x - 7)]
    simp [hx7]