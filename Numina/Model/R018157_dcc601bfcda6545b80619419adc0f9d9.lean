import Mathlib

open Set Real

theorem algebra_186753 {x : ℝ} (hx : x^2 - ⌊x⌋ = 2) :
    x < 2 ↔ x = -1 ∨ x = Real.sqrt 3 := by
  constructor
  · -- Forward implication: assuming x < 2, proving x = -1 or sqrt 3.
    intro h
    have h1 : ⌊x⌋ ≤ (x : ℝ) := by exact Int.floor_le x
    have h2 : (x : ℝ) < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
    have h3 : ⌊x⌋ ≤ 1 := by
      by_contra h4
      push_neg at h4
      have h4' : ⌊x⌋ ≥ 2 := by omega
      have h4'' : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h4'
      nlinarith [show x ^ 2 ≥ (0 : ℝ) from sq_nonneg x, h1, h2, hx, h4'']
    have h4 : ⌊x⌋ ≥ -2 := by
      by_contra h5
      push_neg at h5
      have h5' : ⌊x⌋ ≤ -3 := by omega
      have h5'' : (⌊x⌋ : ℝ) ≤ (-3 : ℝ) := by exact_mod_cast h5'
      nlinarith [show x ^ 2 ≥ (0 : ℝ) from sq_nonneg x, h1, h2, hx, h5'']
    have h5 : ⌊x⌋ = -2 ∨ ⌊x⌋ = -1 ∨ ⌊x⌋ = 0 ∨ ⌊x⌋ = 1 := by 
      omega
    rcases h5 with h5 | h5 | h5 | h5
    · -- ⌊x⌋ = -2
      have h5' : (⌊x⌋ : ℝ) = (-2 : ℝ) := by exact_mod_cast h5
      nlinarith [show x ^ 2 ≥ (0 : ℝ) from sq_nonneg x, h1, h2, hx, h5']
    · -- ⌊x⌋ = -1
      have h5' : (⌊x⌋ : ℝ) = (-1 : ℝ) := by exact_mod_cast h5
      have hx_eq : x ^ 2 = 1 := by linarith [hx, h5']
      have h6 : x = 1 ∨ x = -1 := by
        have h7 : x ^ 2 - 1 = 0 := by linarith
        have h8 : (x - 1) * (x + 1) = 0 := by linarith
        cases' (mul_eq_zero.mp h8) with h9 h10
        · left
          linarith
        · right
          linarith
      cases h6 with
      | inl hx1 =>
        nlinarith
      | inr hx2 =>
        left
        linarith
    · -- ⌊x⌋ = 0
      have h5' : (⌊x⌋ : ℝ) = (0 : ℝ) := by exact_mod_cast h5
      have hx_eq2 : x ^ 2 = 2 := by linarith [hx, h5']
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ)]
    · -- ⌊x⌋ = 1
      have h5' : (⌊x⌋ : ℝ) = (1 : ℝ) := by exact_mod_cast h5
      have hx_eq : x ^ 2 = 3 := by linarith [hx, h5']
      have h6 : x > 0 := by
        nlinarith
      have h7 : x = Real.sqrt 3 := by
        have hx_eq3 : x ^ 2 = (3 : ℝ) := hx_eq
        have h71 : x > 0 := h6
        have h72 : x = Real.sqrt 3 := by
          rw [← hx_eq3]
          field_simp
        linarith
      right
      linarith
  · -- Backward implication: assuming x=-1 or sqrt 3, proving x < 2
    rintro (h | h)
    · -- Case x = -1
      rw [h]
      norm_num
    · -- Case x = Real.sqrt 3
      rw [h]
      have h3 : Real.sqrt 3 < (2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      linarith