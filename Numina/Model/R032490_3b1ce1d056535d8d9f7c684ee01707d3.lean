import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_197955 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ a b, 1 ≤ a ∧ a ≤ b ∧ b ≤ 2 → f a b = 3 / a + b)
  (M m : ℝ)
  (hM : ∃ a b, 1 ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧ f a b = M)
  (hm : ∃ a b, 1 ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧ f a b = m)
  (hMub : ∀ a b, 1 ≤ a ∧ a ≤ b ∧ b ≤ 2 → f a b ≤ M)
  (hmub : ∀ a b, 1 ≤ a ∧ a ≤ b ∧ b ≤ 2 → f a b ≥ m) :
  M - m = 5 - 2 * sqrt 3 := by
  have h1 : f 1 2 = 5 := by
    rw [h₀ 1 2 (by constructor <;> norm_num)]
    norm_num
  have h2 : f (Real.sqrt 3) (Real.sqrt 3) = 2 * Real.sqrt 3 := by
    rw [h₀ (Real.sqrt 3) (Real.sqrt 3) (by
      constructor
      · -- Show $1 \leq \sqrt{3}$.
        have h1 : 1 < Real.sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num)
        linarith
      constructor
      · -- Show $\sqrt{3} \leq \sqrt{3}$.
        linarith
      · -- Show $\sqrt{3} \leq 2$.
        have h2 : Real.sqrt 3 ≤ 2 := by
          rw [Real.sqrt_le_left (by norm_num)]
          all_goals norm_num
        linarith
    )]
    have h3 : Real.sqrt 3 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals
        norm_num
    have h4 : 3 / (Real.sqrt 3 : ℝ) = Real.sqrt 3 := by
      field_simp [Real.sqrt_ne_zero', Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    rw [h4]
    all_goals nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  -- Show M = 5.
  have h3 : M = 5 := by
    have h3 : M ≥ 5 := by
      have h4 : f 1 2 ≤ M := hMub 1 2 (by constructor <;> norm_num)
      have h5 : f 1 2 = 5 := h1
      linarith
    have h4 : M ≤ 5 := by
      rcases hM with ⟨a, b, ha1, ha2, hb, hM_eq⟩
      have h5 : f a b ≤ 5 := by
        rw [h₀ a b ⟨ha1, ha2, hb⟩]
        have h6 : a ≥ 1 := by linarith
        have h7 : b ≤ 2 := by linarith
        have h8 : 3 / a ≤ 3 := by
          have h9 : a ≥ 1 := by linarith
          have h10 : a > 0 := by linarith
          apply (div_le_iff₀ (by linarith)).mpr
          nlinarith
        have h9 : b ≤ 2 := by linarith
        have h10 : 3 / a + b ≤ 5 := by
          nlinarith [show 3 / a ≤ 3 by linarith, show b ≤ 2 by linarith]
        linarith
      linarith [hM_eq, h5]
    linarith
  -- Show m = 2 * sqrt 3.
  have h4 : m = 2 * Real.sqrt 3 := by
    have h5 : m ≤ 2 * Real.sqrt 3 := by
      have h6 : f (Real.sqrt 3) (Real.sqrt 3) ≥ m := hmub (Real.sqrt 3) (Real.sqrt 3) (by
        constructor
        · -- Show $1 \leq \sqrt{3}$.
          have h1 : 1 < Real.sqrt 3 := Real.lt_sqrt_of_sq_lt (by norm_num)
          linarith
        constructor
        · -- Show $\sqrt{3} \leq \sqrt{3}$.
          linarith
        · -- Show $\sqrt{3} \leq 2$.
          have h2 : Real.sqrt 3 ≤ 2 := by
            rw [Real.sqrt_le_left (by norm_num)]
            all_goals norm_num
          linarith
      )
      have h7 : f (Real.sqrt 3) (Real.sqrt 3) = 2 * Real.sqrt 3 := h2
      linarith
    have h6 : m ≥ 2 * Real.sqrt 3 := by
      rcases hm with ⟨a, b, ha1, ha2, hb, hm_eq⟩
      have h8 : f a b ≥ 2 * Real.sqrt 3 := by
        rw [h₀ a b ⟨ha1, ha2, hb⟩]
        have h7 : a ≥ 1 := by linarith
        have h8 : b ≥ a := by linarith
        have h9 : b ≤ 2 := by linarith
        have h10 : 3 / a + b ≥ 2 * Real.sqrt 3 := by
          have h11 : a ≥ 1 := by linarith
          have h12 : b ≥ a := by linarith
          have h13 : (3 / a) + b ≥ (3 / a) + a := by
            have h14 : a ≤ b := by linarith
            have h15 : a ≤ b := by linarith
            have h16 : (3 / a) + a ≤ (3 / a) + b := by
              nlinarith
            linarith
          have h17 : (3 / a) + a ≥ 2 * Real.sqrt 3 := by
            have h3_pos : a > 0 := by linarith
            have h18 : (3 / a) + a - 2 * Real.sqrt 3 ≥ 0 := by
              have h19 : (3 / a) + a - 2 * Real.sqrt 3 = (3 + a ^ 2 - 2 * Real.sqrt 3 * a) / a := by
                field_simp
                <;> ring
              rw [h19]
              apply div_nonneg
              · -- Show numerator is non-negative
                nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (a - Real.sqrt 3), sq_nonneg (a ^ 2 - 3), Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)]
              all_goals linarith
            linarith
          linarith
        linarith
      linarith [hm_eq, h8]
    linarith
  -- Calculate M - m.
  rw [h3, h4]
  all_goals
    all_goals nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]