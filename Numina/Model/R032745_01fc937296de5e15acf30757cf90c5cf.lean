import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_213015 :
  IsGreatest {x | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ x = min (min a (1 / b)) (b + 1 / a)} (Real.sqrt 2) := by
  constructor
  · -- Show that sqrt 2 is in the set
    use Real.sqrt 2, Real.sqrt 2 / 2
    constructor
    · -- Show that sqrt 2 > 0
      positivity
    constructor
    · -- Show that sqrt 2 / 2 > 0
      positivity
    · -- Show that sqrt 2 = min (min (sqrt 2) (1 / (sqrt 2 / 2))) ((sqrt 2 / 2) + 1 / (sqrt 2))
      have h1 : Real.sqrt 2 > 0 := by positivity
      have h2 : (1 / (Real.sqrt 2 / 2) : ℝ) = Real.sqrt 2 := by
        field_simp
      have h3 : (1 / Real.sqrt 2 : ℝ) = Real.sqrt 2 / 2 := by
        field_simp
      have h4 : (Real.sqrt 2 / 2 : ℝ) + 1 / (Real.sqrt 2) = Real.sqrt 2 := by
        rw [h3]
        ring
      rw [h2, h4]
      norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
  · -- Show that sqrt 2 is greatest in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hx⟩
    by_contra h
    push_neg at h
    have h11 : min (min a (1 / b)) (b + 1 / a) > Real.sqrt 2 := by
      linarith
    have h21 : min a (1 / b) > Real.sqrt 2 := by
      by_contra h
      push_neg at h
      have h32 : min (min a (1 / b)) (b + 1 / a) ≤ Real.sqrt 2 := by
        have h34 : min (min a (1 / b)) (b + 1 / a) ≤ min a (1 / b) := by
          apply min_le_left
        nlinarith
      linarith
    have h41 : (1 / b : ℝ) > Real.sqrt 2 := by
      have h22 : a ≥ min a (1 / b) := by
        cases min_cases a (1 / b) with
        | inl h =>
          linarith
        | inr h =>
          linarith
      have h23 : (1 / b) ≥ min a (1 / b) := by
        cases min_cases a (1 / b) with
        | inl h =>
          linarith [h]
        | inr h =>
          linarith
      nlinarith [h21]
    have h10 : a > Real.sqrt 2 := by
      have h22 : a ≥ min a (1 / b) := by
        cases min_cases a (1 / b) with
        | inl h =>
          linarith
        | inr h =>
          linarith
      nlinarith [h21]
    have h12 : (b + 1 / a : ℝ) > Real.sqrt 2 := by
      by_contra h
      push_neg at h
      have h13 : min (min a (1 / b)) (b + 1 / a) ≤ (b + 1 / a : ℝ) := by
        apply min_le_right
      nlinarith
    have h71 : b < Real.sqrt 2 / 2 := by
      have h72 : (1 / b : ℝ) > Real.sqrt 2 := h41
      have h73 : b > 0 := hb
      have h74 : Real.sqrt 2 * b < 1 := by
        by_contra h
        push_neg at h
        have h44 : (1 / b : ℝ) ≤ Real.sqrt 2 := by
          have h45 : Real.sqrt 2 * b ≥ 1 := by linarith [h]
          have h46 : (1 / b : ℝ) ≤ Real.sqrt 2 := by
            apply (div_le_iff₀ (by linarith)).mpr
            nlinarith
          linarith
        linarith
      have h71 : b < Real.sqrt 2 / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith
    have h28 : (1 / a : ℝ) < Real.sqrt 2 / 2 := by
      have h49 : a > Real.sqrt 2 := h10
      have h50 : (1 / a : ℝ) < (1 / (Real.sqrt 2 : ℝ) : ℝ) := by
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        nlinarith
      have h19 : (1 / (Real.sqrt 2 : ℝ) : ℝ) = Real.sqrt 2 / 2 := by
        field_simp
      nlinarith [h19]
    have h36 : (b + 1 / a : ℝ) < Real.sqrt 2 := by
      nlinarith [h71, h28]
    nlinarith