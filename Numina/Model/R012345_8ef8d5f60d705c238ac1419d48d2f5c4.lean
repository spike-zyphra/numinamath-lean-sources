import Mathlib

theorem algebra_119578 (x : ℝ) (hx : x^2 - 6 * ⌊x⌋ + 5 = 0) :
    x = 1 ∨ x = Real.sqrt 7 ∨ x = Real.sqrt 13 ∨ x = Real.sqrt 19 ∨ x = 5 := by
  have h1 : (⌊x⌋ : ℝ) ≤ x := by
    exact Int.floor_le x
  have h2 : x < (⌊x⌋ + 1 : ℝ) := by
    exact Int.lt_floor_add_one x
  have h3 : x^2 = 6 * (⌊x⌋ : ℝ) - 5 := by
    linarith
  have h4 : (⌊x⌋ : ℝ) ≥ (5 / 6 : ℝ) := by
    nlinarith [sq_nonneg x]
  have h5 : ⌊x⌋ ≥ 1 := by
    by_contra h
    push_neg at h
    have h6 : ⌊x⌋ ≤ 0 := by
      omega
    have h7 : (⌊x⌋ : ℝ) ≤ (0 : ℝ) := by
      exact_mod_cast h6
    nlinarith
  have h6 : ⌊x⌋ ≤ 5 := by
    by_contra h
    push_neg at h
    have h7 : ⌊x⌋ ≥ 6 := by
      omega
    have h8 : (⌊x⌋ : ℝ) ≥ (6 : ℝ) := by
      exact_mod_cast h7
    nlinarith [sq_nonneg (x - (⌊x⌋ : ℝ)), sq_nonneg (x + 0), h1, h2]
  have h9 : ⌊x⌋ = 1 ∨ ⌊x⌋ = 2 ∨ ⌊x⌋ = 3 ∨ ⌊x⌋ = 4 ∨ ⌊x⌋ = 5 := by
    omega
  rcases h9 with h9 | h9 | h9 | h9 | h9
  · -- Case ⌊x⌋ = 1
    have h10 : (⌊x⌋ : ℝ) = (1 : ℝ) := by
      exact_mod_cast h9
    have h11 : x^2 = 1 := by
      nlinarith
    have h12 : x = 1 ∨ x = -1 := by
      have h13 : x^2 - 1 = 0 := by
        linarith
      have h14 : (x - 1) * (x + 1) = 0 := by
        linarith
      cases (mul_eq_zero.1 h14) with
      | inl h15 =>
        left
        linarith
      | inr h16 =>
        right
        linarith
    cases h12 with
    | inl h13 =>
      left
      linarith
    | inr h14 =>
      exfalso
      have h15 : (⌊x⌋ : ℝ) = (1 : ℝ) := h10
      nlinarith [Int.floor_le x, Int.lt_floor_add_one x]
  · -- Case ⌊x⌋ = 2
    have h10 : (⌊x⌋ : ℝ) = (2 : ℝ) := by
      exact_mod_cast h9
    have h11 : x^2 = 7 := by
      nlinarith
    have hx2 : x ≥ 2 := by
      nlinarith [sq_nonneg (x - 2), h10, h1, h2]
    have hx3 : x < (3 : ℝ) := by
      nlinarith [h2, h10]
    have hx4 : x = Real.sqrt 7 := by
      have h12 : x^2 = 7 := h11
      have hx5 : x ≥ 0 := by
        nlinarith
      have hx6 : Real.sqrt (x^2) = Real.sqrt (7 : ℝ) := by
        rw [h12]
      have hx7 : Real.sqrt (x ^ 2) = x := by
        rw [Real.sqrt_sq (show 0 ≤ x by nlinarith)]
      have hx8 : x = Real.sqrt (7 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (7 : ℝ)]
      linarith
    right
    left
    exact hx4
  · -- Case ⌊x⌋ = 3
    have h10 : (⌊x⌋ : ℝ) = (3 : ℝ) := by
      exact_mod_cast h9
    have h11 : x^2 = 13 := by
      nlinarith
    have hx2 : x ≥ 3 := by
      nlinarith [sq_nonneg (x - 3), h10, h1, h2]
    have hx3 : x < (4 : ℝ) := by
      nlinarith [h2, h10]
    have hx4 : x = Real.sqrt 13 := by
      have h12 : x^2 = 13 := h11
      have hx5 : x ≥ 0 := by
        nlinarith
      have hx6 : Real.sqrt (x ^ 2) = Real.sqrt (13 : ℝ) := by
        rw [h12]
      have hx7 : Real.sqrt (x ^ 2) = x := by
        rw [Real.sqrt_sq (show 0 ≤ x by nlinarith)]
      have hx8 : x = Real.sqrt (13 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (13 : ℝ)]
      linarith
    right
    right
    left
    exact hx4
  · -- Case ⌊x⌋ = 4
    have h10 : (⌊x⌋ : ℝ) = (4 : ℝ) := by
      exact_mod_cast h9
    have h11 : x^2 = 19 := by
      nlinarith
    have hx2 : x ≥ 4 := by
      nlinarith [sq_nonneg (x - 4), h10, h1, h2]
    have hx3 : x < (5 : ℝ) := by
      nlinarith [h2, h10]
    have hx4 : x = Real.sqrt 19 := by
      have h12 : x^2 = 19 := h11
      have hx5 : x ≥ 0 := by
        nlinarith
      have hx6 : Real.sqrt (x ^ 2) = Real.sqrt (19 : ℝ) := by
        rw [h12]
      have hx7 : Real.sqrt (x ^ 2) = x := by
        rw [Real.sqrt_sq (show 0 ≤ x by nlinarith)]
      have hx8 : x = Real.sqrt (19 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (19 : ℝ)]
      linarith
    right
    right
    right
    left
    exact hx4
  · -- Case ⌊x⌋ = 5
    have h10 : (⌊x⌋ : ℝ) = (5 : ℝ) := by
      exact_mod_cast h9
    have h11 : x^2 = 25 := by
      nlinarith
    have hx2 : x ≥ 5 := by
      nlinarith [sq_nonneg (x - 5), h10, h1, h2]
    have hx3 : x < (6 : ℝ) := by
      nlinarith [h2, h10]
    have hx4 : x = 5 := by
      nlinarith
    right
    right
    right
    right
    exact hx4