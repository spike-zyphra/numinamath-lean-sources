import Mathlib

theorem algebra_4585 :
  IsGreatest {a | ∃ r s : ℝ , (2017)^2 * r^2 - 2018 * 2016 * r - 1 = 0 ∧ 2017 * s^2 + 2018 * s + 1 = 0 ∧ 
  (∃ a b c d e f g h: ℝ, (2017)^2 * r^2 - 2018 * 2016 * r - 1 = (a * r + b) * (c * r + d) ∧ 2017 * s^2 + 2018 * s + 1 = (e * s + f) * (g * s + h))
  ∧ a = r - s} 2 := by
  constructor
  · -- Show 2 is indeed a possible value
    use 1, -1
    refine ⟨by norm_num, by norm_num, (?_ : ∃ a b c d e f g h : ℝ, _ ∧ _), by norm_num⟩ 
    · -- Construct witnesses for the existential quantifier.
      use 0, 0, 0, 0, 0, 0, 0, 0
      constructor <;> norm_num
  · -- Show 2 is greatest
    intro a ha
    rcases ha with ⟨r, s, h1, h2, h3, h4⟩
    rcases h3 with ⟨a, b, c, d, e, f, g, h, hr, hs⟩
    have h1' : (r - 1) * ((2017 : ℝ) ^ 2 * r + 1) = 0 := by
      nlinarith
    have hr1 : r = 1 ∨ r = -1 / (2017 : ℝ) ^ 2 := by
      cases (mul_eq_zero.mp h1') with
      | inl h11 => 
        left
        have : r = 1 := by linarith
        exact this
      | inr h12 =>
        right
        have h_1 : (2017 : ℝ)^2 * r + 1 = 0 := by linarith
        field_simp at h_1 ⊢
        nlinarith
    have h2' : (s + 1) * (2017 * s + 1) = 0 := by
      nlinarith
    have hs1 : s = -1 ∨ s = -1 / 2017 := by 
      cases (mul_eq_zero.mp h2') with
      | inl h21 => 
        left
        linarith
      | inr h22 =>
        right
        have h_1 : 2017 * s + 1 = 0 := by linarith
        field_simp at h_1 ⊢
        nlinarith
    -- Use case analysis to check all 4 combinations
    cases hr1 with
    | inl hr1 => -- r = 1
      cases hs1 with 
      | inl hs1' => -- s = -1
        have h5 : r - s ≤ 2 := by
          rw [hr1, hs1']
          norm_num
        linarith [h5, h4]
      | inr hs1' => -- s = -1/2017
        have h5 : r - s ≤ 2 := by
          rw [hr1, hs1']
          norm_num
        linarith [h5, h4]
    | inr hr1 => -- r = -1/(2017^2)
      cases hs1 with 
      | inl hs1' => -- s = -1
        have h5 : r - s ≤ 2 := by
          rw [hr1, hs1']
          norm_num
        linarith [h5, h4]
      | inr hs1' => -- s = -1/2017
        have h5 : r - s ≤ 2 := by
          rw [hr1, hs1']
          norm_num
        linarith [h5, h4]