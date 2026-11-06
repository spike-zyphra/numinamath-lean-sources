import Mathlib

theorem algebra_19786 : IsGreatest {S | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a ∧ a^2 + b^2 = c^2 ∧ [12, 20] ⊆ [a, b, c] ∧ S = (1/2) * a * b} 120 := by
  constructor
  · -- Show 120 is in the set
    use 12, 20, Real.sqrt 544
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- Show that sqrt(544) is positive
      positivity
    constructor
    · -- Show that sqrt(544) < 32 (since 12 + 20 = 32), so the triangle inequality holds
      nlinarith [Real.sqrt_nonneg 544, Real.sq_sqrt (show 0 ≤ (544 : ℝ) by norm_num)]
    constructor
    · -- Show that sqrt(544) < 32 (since 12 + 20 = 32), so the triangle inequality holds
      nlinarith [Real.sqrt_nonneg 544, Real.sq_sqrt (show 0 ≤ (544 : ℝ) by norm_num)]
    constructor
    · -- Show that sqrt(544) < 32 (since 12 + 20 = 32), so the triangle inequality holds
      nlinarith [Real.sqrt_nonneg 544, Real.sq_sqrt (show 0 ≤ (544 : ℝ) by norm_num)]
    constructor
    · -- Show that 12² + 20² = (sqrt(544))²
      nlinarith [Real.sqrt_nonneg 544, Real.sq_sqrt (show 0 ≤ (544 : ℝ) by norm_num)]
    constructor
    · -- Show that [12, 20] is a subset of [12, 20, sqrt(544)]
      simp
    · -- Show that S = 120
      norm_num
  · -- Show that 120 is greatest
    intro S hS
    rcases hS with ⟨a, b, c, ha, hb, hc, h1, h2, h3, h4, h5, hS⟩
    have h6 : (12 = a ∨ 12 = b ∨ 12 = c) := by
      simp [Set.subset_def, Set.mem_insert_iff, Set.mem_singleton_iff] at h5 ⊢
      tauto
    have h7 : (20 = a ∨ 20 = b ∨ 20 = c) := by
      simp [Set.subset_def, Set.mem_insert_iff, Set.mem_singleton_iff] at h5 ⊢
      tauto
    rcases h6 with (h6 | h6 | h6)
    · -- Case 12 = a
      rcases h7 with (h7 | h7 | h7)
      · -- Case 20 = a
        exfalso
        linarith
      · -- Case 20 = b
        have ha1 : a = 12 := by linarith
        have hb1 : b = 20 := by linarith
        rw [hS, ha1, hb1]
        all_goals norm_num
      · -- Case 20 = c
        have ha1 : a = 12 := by linarith
        have hc1 : c = 20 := by linarith
        have hb1 : b = 16 := by
          nlinarith
        rw [hS, ha1, hb1]
        all_goals norm_num
    · -- Case 12 = b
      rcases h7 with (h7 | h7 | h7)
      · -- Case 20 = a
        have ha1 : a = 20 := by linarith
        have hb1 : b = 12 := by linarith
        rw [hS, ha1, hb1]
        all_goals norm_num
      · -- Case 20 = b
        exfalso
        linarith
      · -- Case 20 = c
        have hb1 : b = 12 := by linarith
        have hc1 : c = 20 := by linarith
        have ha1 : a = 16 := by
          nlinarith
        rw [hS, ha1, hb1]
        all_goals norm_num
    · -- Case 12 = c
      rcases h7 with (h7 | h7 | h7)
      · -- Case 20 = a
        have ha1 : a = 20 := by linarith
        have hc1 : c = 12 := by linarith
        nlinarith
      · -- Case 20 = b
        have hb1 : b = 20 := by linarith
        have hc1 : c = 12 := by linarith
        nlinarith
      · -- Case 20 = c
        exfalso
        linarith