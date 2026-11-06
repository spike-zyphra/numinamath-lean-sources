import Mathlib

theorem algebra_10184 (x : ℝ) (hx : x^2 - 2 * ⌊x⌋ - 3 = 0) :
    x = -1 ∨ x = Real.sqrt 7 ∨ x = 3 := by
  let n := ⌊x⌋
  have h1 : n ≤ (x : ℝ) := by
    exact Int.floor_le x
  have h2 : (x : ℝ) < (n + 1 : ℝ) := by
    exact Int.lt_floor_add_one x
  have h3 : (x : ℝ)^2 = 2 * (n : ℝ) + 3 := by
    have h_eq : (x : ℝ) ^ 2 - 2 * (n : ℝ) - 3 = (0 : ℝ) := by
      have hn : (n : ℝ) = (⌊x⌋ : ℝ) := by
        simp [n]
      rw [hn] at *
      linarith [hx]
    linarith
  have h4 : n ≤ 3 := by
    by_contra h
    push_neg at h
    have h7 : n ≥ 4 := by
      omega
    have h8 : (n : ℝ) ≥ (4 : ℝ) := by
      exact_mod_cast (show n ≥ 4 from by
        omega
      )
    have h9 : (x : ℝ) ≥ (n : ℝ) := by linarith [h1]
    have h10 : (x : ℝ) ≥ (4 : ℝ) := by linarith [h9, h8]
    have h11 : (x : ℝ) ^ 2 ≥ (16 : ℝ) := by nlinarith
    nlinarith
  have h5 : n ≤ 3 := h4
  have h6 : n ≥ -1 := by
    by_contra h
    push_neg at h
    have h7 : n ≤ -2 := by
      omega
    have h8 : (n : ℝ) ≤ (-2 : ℝ) := by
      exact_mod_cast h7
    have h9 : (x : ℝ) < (n + 1 : ℝ) := by linarith [h2]
    have h10 : (n + 1 : ℝ) ≤ (-1 : ℝ) := by
      nlinarith
    have h11 : (x : ℝ) < (-1 : ℝ) := by
      linarith [h9, h10]
    nlinarith
  have h7 : n ≥ -1 := h6
  have h8 : n ≤ 3 := h4
  have h9 : n = -1 ∨ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases h9 with (r | r | r | r | r)
  · -- When n = -1
    have hn : (n : ℝ) = -1 := by
      exact_mod_cast r
    have h10 : (x : ℝ) ^ 2 = 1 := by
      rw [hn] at h3
      nlinarith
    have h11 : (x : ℝ) = -1 := by
      nlinarith [sq_nonneg (x + 1)]
    left
    linarith
  · -- When n = 0
    have hn : (n : ℝ) = 0 := by
      exact_mod_cast r
    have h12 : (x : ℝ) ^ 2 = 3 := by
      rw [hn] at h3
      nlinarith
    nlinarith [sq_nonneg (x - 1)]
  · -- When n = 1
    have hn : (n : ℝ) = 1 := by
      exact_mod_cast r
    have h13 : (x : ℝ) ^ 2 = 5 := by
      rw [hn] at h3
      nlinarith
    nlinarith [sq_nonneg (x - 2)]
  · -- When n = 2
    have hn : (n : ℝ) = 2 := by
      exact_mod_cast r
    have h14 : (x : ℝ) ^ 2 = 7 := by
      rw [hn] at h3
      nlinarith
    have h15 : x = Real.sqrt 7 := by
      have h16 : x ≥ (2 : ℝ) := by
        linarith [h1, hn]
      have h17 : Real.sqrt 7 ≥ (2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
      have h18 : x = Real.sqrt 7 := by
        nlinarith [sq_nonneg (x - Real.sqrt 7), Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
      linarith
    right
    left
    exact_mod_cast h15
  · -- When n = 3
    have hn : (n : ℝ) = 3 := by
      exact_mod_cast r
    have h16 : (x : ℝ) ^ 2 = 9 := by
      rw [hn] at h3
      nlinarith
    have h17 : x = (3 : ℝ) := by
      have h18 : x ≥ (3 : ℝ) := by
        linarith [h1, hn]
      nlinarith [sq_nonneg (x - 3)]
    right
    right
    linarith