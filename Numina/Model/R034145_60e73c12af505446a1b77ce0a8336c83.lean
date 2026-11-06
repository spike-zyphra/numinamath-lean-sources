import Mathlib

open Set Real

theorem algebra_279114 {x : ℝ} (hx : x^2 - ⌊x⌋ = 2 ∧ -2 < x ∧ x < 2) :
    x = -1 ∨ x = sqrt 3 := by
  rcases hx with ⟨h1, h2, h3⟩
  have h4 : ⌊x⌋ ≤ 1 := by
    by_contra h
    push_neg at h
    have h5 : ⌊x⌋ ≥ 2 := by omega
    have h6 : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by
      exact_mod_cast h5
    nlinarith
  have h7 : ⌊x⌋ ≥ -2 := by
    by_contra h
    push_neg at h
    have h10 : ⌊x⌋ ≤ -3 := by omega
    have h11 : (⌊x⌋ : ℝ) ≤ (-3 : ℝ) := by 
      exact_mod_cast h10
    nlinarith
  have h8 : ⌊x⌋ = -2 ∨ ⌊x⌋ = -1 ∨ ⌊x⌋ = 0 ∨ ⌊x⌋ = 1 := by 
    omega
  rcases h8 with (h9 | h9 | h9 | h9)
  · -- Case ⌊x⌋ = -2
    have h10 : (⌊x⌋ : ℝ) = (-2 : ℝ) := by 
      exact_mod_cast h9
    rw [h10] at h1
    have h11 : x ^ 2 = (0 : ℝ) := by 
      nlinarith
    have h12 : x = (0 : ℝ) := by 
      nlinarith
    -- floor x = -2 requires x in (-2, -1)
    -- but we get x = 0: contradiction
    have h13 : x ≥ (-2 : ℝ) := by 
      have h14 : ⌊x⌋ = -2 := by
        exact_mod_cast h9
      have h15 : x ≥ (⌊x⌋ : ℝ) := by
        exact Int.floor_le x
      rw [show (⌊x⌋ : ℝ) = (-2 : ℝ) by 
        exact_mod_cast h14] at h15
      linarith
    -- upper bound
    have h14 : x < (-1 : ℝ) := by 
      have h15 : ⌊x⌋ = -2 := by
        exact_mod_cast h9
      have h16 : x < (⌊x⌋ + 1 : ℝ) := by 
        exact Int.lt_floor_add_one x
      rw [show (⌊x⌋ : ℝ) = (-2 : ℝ) by 
        exact_mod_cast h15] at h16
      linarith
    linarith [h12, h13, h14]
  · -- Case ⌊x⌋ = -1
    have h10 : (⌊x⌋ : ℝ) = (-1 : ℝ) := by 
      exact_mod_cast h9
    rw [h10] at h1
    -- x^2 =1
    have h11 : x ^ 2 = (1 : ℝ) := by 
      nlinarith
    -- x=1 or x=-1
    have h12 : x = (1 : ℝ) ∨ x = (-1 : ℝ) := by 
      have : x ^ 2 - (1 : ℝ) = 0 := by
        linarith
      have : (x - 1) * (x + 1) = 0 := by
        linarith
      cases' (mul_eq_zero.mp this) with h4 h5
      · -- x - 1 = 0
        left
        linarith
      · -- x + 1 = 0
        right
        linarith
    cases h12 with
    | inl h =>
      -- x=1: this would imply floor x=1, not -1: contradiction
      exfalso
      have h13 : ⌊x⌋ = -1 := by 
        exact_mod_cast h9
      have h14 : x < (0 : ℝ) := by 
        have h15 : ⌊x⌋ = -1 := by 
          exact_mod_cast h9
        have h16 : x < (⌊x⌋ + 1 : ℝ) := by 
          exact Int.lt_floor_add_one x
        rw [show (⌊x⌋ : ℝ) = (-1 : ℝ) by 
          exact_mod_cast h15] at h16
        linarith
      nlinarith [h, h14]
    | inr h =>
      -- x=-1, which is our claimed solution
      left
      linarith
  · -- Case ⌊x⌋ = 0
    have h10 : (⌊x⌋ : ℝ) = (0 : ℝ) := by 
      exact_mod_cast h9
    rw [h10] at h1
    -- $x^2 = 2$: impossible with $x < 1$
    have h11 : x ^ 2 = (2 : ℝ) := by 
      nlinarith
    -- 
    have h12 : x ≥ (0 : ℝ) := by 
      have h13 : ⌊x⌋ = (0 : Int) := h9
      have h14 : x ≥ (⌊x⌋ : ℝ) := by 
        exact Int.floor_le x
      rw [show (⌊x⌋ : ℝ) = (0 : ℝ) by 
        exact_mod_cast h13] at h14
      linarith
    -- 
    have h13 : x < (1 : ℝ) := by 
      have h17 : ⌊x⌋ = (0 : Int) := h9
      have h18 : x < (⌊x⌋ + 1 : ℝ) := by 
        exact Int.lt_floor_add_one x
      rw [show (⌊x⌋ : ℝ) = (0 : ℝ) by 
        exact_mod_cast h17] at h18
      linarith
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  · -- Case ⌊x⌋ = 1
    have h10 : (⌊x⌋ : ℝ) = (1 : ℝ) := by 
      exact_mod_cast h9
    rw [h10] at h1
    -- $x^2 = 3$, leading to $x = \sqrt{3}$, which is our claimed solution
    have h11 : x ^ 2 = (3 : ℝ) := by 
      nlinarith
    -- 
    have h12 : x ≥ (1 : ℝ) := by
      have h13 : ⌊x⌋ = (1 : Int) := h9
      have h14 : x ≥ (⌊x⌋ : ℝ) := by 
        exact Int.floor_le x
      rw [show (⌊x⌋ : ℝ) = (1 : ℝ) by 
        exact_mod_cast h13] at h14
      linarith
    -- 
    have h13 : x < (2 : ℝ) := h3
    -- 
    have h14 : x = Real.sqrt 3 := by
      have h15 : x ≥ 0 := by nlinarith
      have h16 : (x) ^ 2 = (3 : ℝ) := h11
      have h17 : x = Real.sqrt 3 := by
        rw [←h16]
        field_simp
      exact h17
    -- 
    right
    exact h14