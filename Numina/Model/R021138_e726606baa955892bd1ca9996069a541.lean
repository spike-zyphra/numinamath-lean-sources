import Mathlib

theorem algebra_319086 (x : ℝ) :
    x^2 - 2 * ⌊x⌋ - 5 = 0 ↔ x = Real.sqrt 11 := by
  constructor
  · -- Assume x^2 - 2 * ⌊x⌋ - 5 = 0 prove x = Real.sqrt 11
    intro h
    have h1 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
    have h2 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
    have h3 : ⌊x⌋ ≤ 3 := by
      by_contra h4
      push_neg at h4
      have h4' : ⌊x⌋ ≥ 4 := by omega
      have h4'' : (⌊x⌋ : ℝ) ≥ (4 : ℝ) := by exact_mod_cast h4'
      nlinarith [h, h1, h2, h4'']
    have h4 : ⌊x⌋ ≥ -2 := by
      by_contra h5
      push_neg at h5
      have h5' : ⌊x⌋ ≤ -3 := by omega
      have h5'' : (⌊x⌋ : ℝ) ≤ (-3 : ℝ) := by exact_mod_cast h5'
      nlinarith [h, h1, h2, h5'']
    have h5 : ⌊x⌋ = 3 ∨ ⌊x⌋ = 2 ∨ ⌊x⌋ = 1 ∨ ⌊x⌋ = 0 ∨ ⌊x⌋ = -1 ∨ ⌊x⌋ = -2 := by
      omega
    rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5)
    · -- ⌊x⌋ = 3
      have h6 : (⌊x⌋ : ℝ) = (3 : ℝ) := by exact_mod_cast h5
      have h7 : x ^ 2 = (11 : ℝ) := by
        nlinarith [h, h6]
      have h8 : x ≥ (3 : ℝ) := by
        nlinarith [h1, h6]
      have h9 : x < (4 : ℝ) := by
        nlinarith [h2, h6]
      have h10 : x = Real.sqrt 11 := by
        have h11 : x ≥ 0 := by nlinarith
        have h12 : x ^ 2 = (11 : ℝ) := h7
        have : x = Real.sqrt 11 := by
          rw [← h12]
          field_simp
        exact_mod_cast this
      exact_mod_cast h10
    · -- ⌊x⌋ = 2
      have h6 : (⌊x⌋ : ℝ) = (2 : ℝ) := by exact_mod_cast h5
      have h7 : x ^ 2 = (9 : ℝ) := by
        nlinarith [h, h6]
      have h8 : x ≥ (2 : ℝ) := by
        nlinarith [h1, h6]
      have h9 : x < (3 : ℝ) := by
        nlinarith [h2, h6]
      nlinarith [Real.sqrt_nonneg (11 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
    · -- ⌊x⌋ = 1
      have h6 : (⌊x⌋ : ℝ) = (1 : ℝ) := by exact_mod_cast h5
      have h7 : x ^ 2 = (7 : ℝ) := by
        nlinarith [h, h6]
      have h8 : x ≥ (1 : ℝ) := by
        nlinarith [h1, h6]
      have h9 : x < (2 : ℝ) := by
        nlinarith [h2, h6]
      nlinarith [Real.sqrt_nonneg (11 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
    · -- ⌊x⌋ = 0
      have h6 : (⌊x⌋ : ℝ) = (0 : ℝ) := by exact_mod_cast h5
      have h7 : x ^ 2 = (5 : ℝ) := by
        nlinarith [h, h6]
      have h8 : x ≥ (0 : ℝ) := by
        nlinarith [h1, h6]
      have h9 : x < (1 : ℝ) := by
        nlinarith [h2, h6]
      nlinarith [Real.sqrt_nonneg (11 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
    · -- ⌊x⌋ = -1
      have h6 : (⌊x⌋ : ℝ) = (-1 : ℝ) := by exact_mod_cast h5
      have h7 : x ^ 2 = (3 : ℝ) := by
        nlinarith [h, h6]
      have h8 : x ≥ (-1 : ℝ) := by
        nlinarith [h1, h6]
      have h9 : x < (0 : ℝ) := by
        nlinarith [h2, h6]
      nlinarith [Real.sqrt_nonneg (11 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
    · -- ⌊x⌋ = -2
      have h6 : (⌊x⌋ : ℝ) = (-2 : ℝ) := by exact_mod_cast h5
      have h7 : x ^ 2 = (1 : ℝ) := by
        nlinarith [h, h6]
      have h8 : x ≥ (-2 : ℝ) := by
        nlinarith [h1, h6]
      have h9 : x < (-1 : ℝ) := by
        nlinarith [h2, h6]
      nlinarith [Real.sqrt_nonneg (11 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
  · -- Assume x = Real.sqrt 11 prove x^2 - 2 * ⌊x⌋ - 5 = 0
    intro h
    rw [h]
    have h6 : ⌊(Real.sqrt 11 : ℝ)⌋ = 3 := by
      have h1 : 3 < Real.sqrt 11 := by
        rw [Real.lt_sqrt] <;> norm_num
      have h2 : Real.sqrt 11 < (4 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try linarith
    rw [h6]
    have h7 : (Real.sqrt 11 : ℝ) ^ 2 = 11 := Real.sq_sqrt (by norm_num)
    norm_num at h7 ⊢
    <;> nlinarith [Real.sqrt_nonneg 11, h7]