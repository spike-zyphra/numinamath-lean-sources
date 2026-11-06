import Mathlib

theorem algebra_323173 (x : ℝ) :
    ⌊|x^2 - 1|⌋ = 10 ↔
    (x ∈ Set.Ioc (-2 * Real.sqrt 3) (-Real.sqrt 11) ∪ Set.Ico (Real.sqrt 11) (2 * Real.sqrt 3)) := by
  simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ico]
  constructor
  · -- Assume ⌊|x^2 - 1|⌋ = 10, prove (x ∈ Set.Ioc (-2 * Real.sqrt 3) (-Real.sqrt 11) ∪ Set.Ico (Real.sqrt 11) (2 * Real.sqrt 3))
    intro h
    have h1 : 10 ≤ |x^2 - 1| := by
      have h1 : (⌊|x^2 - 1|⌋ : ℝ) ≤ |x^2 - 1| := by
        exact Int.floor_le (|x^2 - 1| : ℝ)
      have h2 : (⌊|x^2 - 1|⌋ : ℝ) ≥ (10 : ℝ) := by
        have h3 : ⌊|x^2 - 1|⌋ ≥ 10 := by linarith
        exact_mod_cast h3
      linarith
    have h2 : |x^2 - 1| < 11 := by
      have h3 : (⌊|x^2 - 1|⌋ : ℝ) < (⌊|x^2 - 1|⌋ + 1 : ℝ) := by
        linarith
      have h4 : |x^2 - 1| < (⌊|x^2 - 1|⌋ + 1 : ℝ) := by
        exact Int.lt_floor_add_one (|x^2 - 1| : ℝ)
      have h5 : ⌊|x^2 - 1|⌋ + 1 = 11 := by
        omega
      have h6 : (⌊|x^2 - 1|⌋ + 1 : ℝ) = (11 : ℝ) := by
        exact_mod_cast h5
      linarith
    by_cases h5 : x^2 - 1 ≥ 0
    · -- Case where x^2 - 1 ≥ 0, so |x^2 - 1| = x^2 - 1
      rw [abs_of_nonneg h5] at h1 h2
      have h6 : 11 ≤ x^2 := by linarith
      have h7 : x^2 < 12 := by linarith
      by_cases h8 : x ≥ 0
      · -- x ≥ 0, so x is in [sqrt 11, 2*sqrt 3)
        have h9 : Real.sqrt 11 ≤ x := by nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
        have h10 : x < 2 * Real.sqrt 3 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        right
        exact ⟨h9, h10⟩
      · -- x < 0, so x is in (-2*sqrt 3, -sqrt 11]
        have h9 : x < 0 := by nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 11 by norm_num), Real.sqrt_nonneg 11]
        have h10 : -x ≥ Real.sqrt 11 := by nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
        have h11 : x ≤ -Real.sqrt 11 := by linarith
        have h12 : x > -2 * Real.sqrt 3 := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        left
        exact ⟨h12, h11⟩
    · -- Case where x^2 - 1 < 0, so |x^2 - 1| = 1 - x^2
      rw [abs_of_neg (lt_of_not_ge h5)] at h1 h2
      nlinarith [sq_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
  · -- Assume (x ∈ Set.Ioc (-2 * Real.sqrt 3) (-Real.sqrt 11) ∪ Set.Ico (Real.sqrt 11) (2 * Real.sqrt 3)), prove ⌊|x^2 - 1|⌋ = 10
    rintro (h | h)
    · -- Case where x ∈ (-2 * Real.sqrt 3, -Real.sqrt 11]
      rcases h with ⟨h1, h2⟩
      have h3 : x < 0 := by nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 11 by norm_num), Real.sqrt_nonneg 11]
      have h4 : x^2 ≥ 11 := by nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num), sq_nonneg x]
      have h5 : x^2 < 12 := by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg x]
      have h6 : |x^2 - 1| ≥ 10 := by
        have h7 : x^2 - 1 ≥ 10 := by nlinarith
        rw [abs_of_nonneg (by nlinarith : x^2 - 1 ≥ 0)]
        linarith
      have h7 : |x^2 - 1| < 11 := by
        have h8 : x^2 - 1 < 11 := by nlinarith
        rw [abs_of_nonneg (by nlinarith : x^2 - 1 ≥ 0)]
        linarith
      have h8 : ⌊|x^2 - 1|⌋ = 10 := by
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith
      exact h8
    · -- Case where x ∈ [Real.sqrt 11, 2 * Real.sqrt 3)
      rcases h with ⟨h1, h2⟩
      have h3 : x ≥ 0 := by nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 11 by norm_num), Real.sqrt_nonneg 11]
      have h4 : x^2 ≥ 11 := by nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num), sq_nonneg x]
      have h5 : x^2 < 12 := by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg x]
      have h6 : |x^2 - 1| ≥ 10 := by
        have h7 : x^2 - 1 ≥ 10 := by nlinarith
        rw [abs_of_nonneg (by nlinarith : x^2 - 1 ≥ 0)]
        linarith
      have h7 : |x^2 - 1| < 11 := by
        have h8 : x^2 - 1 < 11 := by nlinarith
        rw [abs_of_nonneg (by nlinarith : x^2 - 1 ≥ 0)]
        linarith
      have h8 : ⌊|x^2 - 1|⌋ = 10 := by
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> nlinarith
      exact h8