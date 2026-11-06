import Mathlib

lemma lemma_1 (y : ℝ) :
    ⌊y⌋ = 10 ↔ 10 ≤ y ∧ y < 11 := by
  constructor
  ·
    intro h
    have h1 : (10 : ℝ) ≤ y := by
      have h2 : (⌊y⌋ : ℝ) ≤ y := by
        exact Int.floor_le y
      rw [show ⌊y⌋ = 10 by omega] at h2
      norm_num at h2 ⊢
      linarith
    have h2 : y < (11 : ℝ) := by
      have h3 : y < (⌊y⌋ + 1 : ℝ) := by
        exact Int.lt_floor_add_one y
      rw [show ⌊y⌋ = 10 by omega] at h3
      norm_num at h3 ⊢
      linarith
    constructor <;> try linarith
  ·
    rintro ⟨h1, h2⟩
    have h3 : ⌊y⌋ = 10 := by
      have h4 : ⌊y⌋ ≤ 10 := by
        by_contra h
        push_neg at h
        have h5 : ⌊y⌋ ≥ 11 := by omega
        have h6 : (⌊y⌋ : ℝ) ≥ (11 : ℝ) := by exact_mod_cast h5
        have h7 : (⌊y⌋ : ℝ) ≤ y := by
          exact Int.floor_le y
        have h8 : y ≥ (11 : ℝ) := by linarith [h6, h7]
        linarith
      have h9 : ⌊y⌋ ≥ 10 := by
        by_contra h
        push_neg at h
        have h10 : ⌊y⌋ ≤ 9 := by omega
        have h11 : (⌊y⌋ : ℝ) ≤ (9 : ℝ) := by exact_mod_cast h10
        have h12 : y < (⌊y⌋ + 1 : ℝ) := by
          exact Int.lt_floor_add_one y
        have h14 : y < (10 : ℝ) := by
          nlinarith
        linarith
      omega
    exact h3

theorem algebra_139523 (x : ℝ) :
    ⌊|x^2 - 1|⌋ = 10 ↔ x ∈ Set.Ioc (-2 * Real.sqrt 3) (-Real.sqrt 11) ∪ Set.Ico (Real.sqrt 11) (2 * Real.sqrt 3) := by
  constructor
  · -- Forward direction: $\lfloor |x^2-1| \rfloor = 10$ implies $x \in (-2\sqrt{3}, -\sqrt{11}] \cup [\sqrt{11}, 2\sqrt{3})$
    intro h
    rw [lemma_1] at h
    rcases h with ⟨h1, h2⟩
    have h3 : 10 ≤ |x^2 - 1| := by linarith
    have h4 : |x^2 - 1| < 11 := by linarith
    cases' abs_cases (x^2 - 1) with h5 h5
    · -- Case where $|x^2 - 1| = x^2 - 1$
      have h6 : 10 ≤ x^2 - 1 := by linarith
      have h7 : x^2 - 1 < 11 := by linarith
      have h8 : x^2 ≥ 11 := by linarith
      have h9 : x^2 < 12 := by linarith
      have h10 : x ≤ -Real.sqrt 11 ∨ x ≥ Real.sqrt 11 := by
        by_cases h12 : x ≥ 0
        · -- If x ≥ 0, then x^2 ≥ 11 implies x ≥ sqrt(11)
          right
          nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
        · -- x < 0
          left
          nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]
      have h12 : -2 * Real.sqrt 3 < x := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num)]
      have h13 : x < 2 * Real.sqrt 3 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num)]
      rcases h10 with h14 | h14
      · -- x ≤ -sqrt(11)
        left
        constructor
        · -- Show -2 * sqrt 3 < x
          nlinarith
        · -- Show x ≤ -sqrt 11
          nlinarith
      · -- x ≥ sqrt(11)
        right
        constructor
        · -- Show sqrt 11 ≤ x
          nlinarith
        · -- Show x < 2 * sqrt 3
          nlinarith
    · -- Case where $|x^2 - 1| = -(x^2 - 1) = 1 - x^2$
      have h6 : 10 ≤ 1 - x^2 := by linarith
      nlinarith [sq_nonneg x]
  · -- Backward direction: $x \in (-2\sqrt{3}, -\sqrt{11}] \cup [\sqrt{11}, 2\sqrt{3})$ implies $\lfloor |x^2-1| \rfloor = 10$
    intro h
    rcases h with (h | h)
    · -- Case where x ∈ (-2 * sqrt 3, -sqrt 11]
      rcases h with ⟨h1, h2⟩
      have h3 : -2 * Real.sqrt 3 < x := by linarith
      have h4 : x ≤ -Real.sqrt 11 := by linarith
      have h5 : x^2 ≥ 11 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num)]
      have h6 : x^2 < 12 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num)]
      have h7 : 10 ≤ |x^2 - 1| := by
        have h8 : x^2 - 1 ≥ 10 := by
          nlinarith
        have h9 : |x^2 - 1| = x^2 - 1 := by
          apply abs_of_nonneg
          nlinarith
        linarith
      have h8 : |x^2 - 1| < 11 := by
        have h9 : x^2 - 1 < 11 := by
          nlinarith
        have h10 : |x^2 - 1| = x^2 - 1 := by
          apply abs_of_nonneg
          nlinarith
        linarith
      rw [lemma_1]
      constructor <;> try linarith
    · -- Case where x ∈ [sqrt 11, 2 * sqrt 3)
      rcases h with ⟨h1, h2⟩
      have h3 : Real.sqrt 11 ≤ x := by linarith
      have h4 : x < 2 * Real.sqrt 3 := by linarith
      have h5 : x^2 ≥ 11 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num)]
      have h6 : x^2 < 12 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 11 by norm_num)]
      have h7 : 10 ≤ |x^2 - 1| := by
        have h8 : x^2 - 1 ≥ 10 := by
          nlinarith
        have h9 : |x^2 - 1| = x^2 - 1 := by
          apply abs_of_nonneg
          nlinarith
        linarith
      have h8 : |x^2 - 1| < 11 := by
        have h9 : x^2 - 1 < 11 := by
          nlinarith
        have h10 : |x^2 - 1| = x^2 - 1 := by
          apply abs_of_nonneg
          nlinarith
        linarith
      rw [lemma_1]
      constructor <;> try linarith