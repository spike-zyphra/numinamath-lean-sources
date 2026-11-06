import Mathlib

open BigOperators Real Set


theorem algebra_10821 {x : ℝ} :
  ⌊abs (x^2 - 1)⌋ = 10 ↔
  (x ∈ Ioc (-2*sqrt 3) (-sqrt 11) ∪ Ico (sqrt 11) (2*sqrt 3)) := by
  constructor
  · -- Forward: ⌊abs (x^2 - 1)⌋ = 10 → (x ∈ Ioc (-2*sqrt 3) (-sqrt 11) ∪ Ico (sqrt 11) (2*sqrt 3))
    intro h
    have h1 : 10 ≤ abs (x ^ 2 - 1) := by
      have h2 : ⌊abs (x^2 - 1)⌋ = 10 := h
      have h3 : 10 ≤ abs (x ^ 2 - 1) := by
        have h4 : (⌊abs (x^2 - 1)⌋ : ℝ) ≤ abs (x^2 - 1) := by
          exact Int.floor_le (abs (x^2 - 1))
        have h6 : ⌊abs (x^2 - 1)⌋ = 10 := h2
        rw [show (⌊abs (x^2 - 1)⌋ : ℝ) = (10 : ℝ) by exact_mod_cast h6] at h4
        linarith
      linarith
    have h2 : abs (x ^ 2 - 1) < 11 := by
      have h3 : ⌊abs (x^2 - 1)⌋ = 10 := h
      have h4 : abs (x ^ 2 - 1) < (11 : ℝ) := by
        have h5 : abs (x ^ 2 - 1) < (⌊abs (x^2 - 1)⌋ + 1 : ℝ) := by
          exact Int.lt_floor_add_one (abs (x^2 - 1))
        have h6 : ⌊abs (x^2 - 1)⌋ = 10 := h3
        rw [show (⌊abs (x^2 - 1)⌋ + 1 : ℝ) = (11 : ℝ) by
          have h9 : ⌊abs (x^2 - 1)⌋ = 10 := h3
          rw [show ⌊abs (x^2 - 1)⌋ = (10 : ℤ) by linarith [h9]]
          norm_num
        ] at h5
        linarith
      linarith
    by_cases h5 : x^2 - 1 ≥ 0
    · -- x^2 - 1 ≥ 0. Then |x^2 -1| = x^2 -1.
      rw [abs_of_nonneg h5] at h1 h2
      have h11 : 11 ≤ x^2 := by linarith
      have h12 : x^2 < 12 := by linarith
      have h21 : |x| < 2 * sqrt 3 := by
        have h22 : |x| ^ 2 < (12 : ℝ) := by
          have h23 : |x| ^ 2 = x^2 := by
            simp [sq_abs]
          linarith
        have h24 : (2 * sqrt 3) ^ 2 = (12 : ℝ) := by
          calc
            (2 * sqrt 3) ^ 2 = 4 * (sqrt 3) ^ 2 := by ring
            _ = 4 * (3 : ℝ) := by rw [Real.sq_sqrt]; positivity
            _ = (12 : ℝ) := by norm_num
        have h25 : |x| ≥ 0 := abs_nonneg x
        have h26 : (2 * sqrt 3) ≥ 0 := by positivity
        nlinarith [Real.sqrt_nonneg 3, sq_nonneg (|x| - 2 * sqrt 3)]
      have h13 : sqrt 11 ≤ |x| := by
        have h14 : (sqrt 11) ^ 2 = (11 : ℝ) := by
          rw [Real.sq_sqrt]
          all_goals norm_num
        have h15 : |x| ^ 2 = x^2 := by
          simp [sq_abs]
        have h16 : (sqrt 11) ^ 2 ≤ |x| ^ 2 := by
          nlinarith
        have h17 : 0 ≤ (sqrt 11 : ℝ) := Real.sqrt_nonneg 11
        have h18 : 0 ≤ |x| := abs_nonneg x
        nlinarith [Real.sqrt_nonneg 11, sq_nonneg (|x| - sqrt 11)]
      cases' abs_cases x with hx hx
      · -- x ≥ 0.
        have h27 : sqrt 11 ≤ x := by linarith [h13]
        have h28 : x < 2 * sqrt 3 := by linarith [h21]
        right
        exact ⟨by linarith, by linarith⟩
      · -- x < 0.
        have h29 : sqrt 11 ≤ -x := by linarith [h13]
        have h30 : -x < 2 * sqrt 3 := by linarith [h21]
        have h31 : -2 * sqrt 3 < x := by nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 11]
        have h32 : x ≤ -sqrt 11 := by nlinarith [Real.sqrt_nonneg 11]
        left
        exact ⟨by linarith, by linarith⟩
    · -- x^2 - 1 < 0. Then |x^2 - 1| = 1 - x^2.
      rw [abs_of_neg (show x^2 - 1 < 0 by linarith)] at h1 h2
      nlinarith [show x^2 ≥ 0 by nlinarith, Real.sqrt_nonneg 3, Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
  · -- Backward: (x ∈ Ioc (-2*sqrt 3) (-sqrt 11) ∪ Ico (sqrt 11) (2*sqrt 3)) → ⌊abs (x^2 - 1)⌋ = 10
    rintro (h | h)
    · -- x ∈ (-2*sqrt 3, -sqrt 11]
      rcases h with ⟨h1, h2⟩
      have h3 : -2 * sqrt 3 < x := h1
      have h4 : x ≤ -sqrt 11 := h2
      have h5 : x^2 ≥ 11 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
      have h6 : x^2 < 12 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
      have h7 : abs (x^2 - 1) = x^2 - 1 := by
        rw [abs_of_nonneg (show x^2 - 1 ≥ 0 by nlinarith)]
      rw [h7]
      have h8 : 10 ≤ x^2 - 1 := by nlinarith
      have h9 : x^2 - 1 < 11 := by nlinarith
      have h10 : ⌊x^2 - 1⌋ = 10 := by
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith
      exact_mod_cast h10
    · -- x ∈ [sqrt 11, 2*sqrt 3)
      rcases h with ⟨h1, h2⟩
      have h3 : sqrt 11 ≤ x := h1
      have h4 : x < 2 * sqrt 3 := h2
      have h5 : x^2 ≥ 11 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
      have h6 : x^2 < 12 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
      have h7 : abs (x^2 - 1) = x^2 - 1 := by
        rw [abs_of_nonneg (show x^2 - 1 ≥ 0 by nlinarith)]
      rw [h7]
      have h8 : 10 ≤ x^2 - 1 := by nlinarith
      have h9 : x^2 - 1 < 11 := by nlinarith
      have h10 : ⌊x^2 - 1⌋ = 10 := by
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith
      exact_mod_cast h10