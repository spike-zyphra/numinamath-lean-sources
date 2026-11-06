import Mathlib

theorem algebra_20534 (a b : ℝ) (h : {x : ℝ | -4 < 2 * (x - 1) ∧ 2 * (x - 1) < 8} = {x | a < x ∧ x < b}) :
    a + b = 4 := by

  have h1 : (0 : ℝ) ∈ {x : ℝ | -4 < 2 * (x - 1) ∧ 2 * (x - 1) < 8} := by
    constructor
    · norm_num
    · norm_num
  have h1' : (0 : ℝ) ∈ {x | a < x ∧ x < b} := by
    rw [h] at *
    exact h1
  rcases h1' with ⟨h2, h3⟩

  have h4 : (4 : ℝ) ∈ {x : ℝ | -4 < 2 * (x - 1) ∧ 2 * (x - 1) < 8} := by
    constructor
    · norm_num
    · norm_num
  have h4' : (4 : ℝ) ∈ {x | a < x ∧ x < b} := by
    rw [h] at *
    exact h4
  rcases h4' with ⟨h5, h6⟩

  have ha1 : a ≤ -1 := by
    by_contra h7
    push_neg at h7
    have h8 : a > -1 := by linarith
    have h9 : (-1 + (a + 1)/2 : ℝ) ∈ {x : ℝ | -4 < 2 * (x - 1) ∧ 2 * (x - 1) < 8} := by
      constructor
      ·
        -- Show $-4 < 2 * ((-1 + (a + 1)/2) - 1)$
        have h10 : -4 < 2 * ((-1 + (a + 1)/2 : ℝ) - 1) := by
          nlinarith
        linarith
      ·
        -- Show $2 * ((-1 + (a + 1)/2) - 1) < 8$
        have h11 : 2 * ((-1 + (a + 1)/2 : ℝ) - 1) < 8 := by
          nlinarith
        linarith
    have h10 : (-1 + (a + 1)/2 : ℝ) ∈ {x : ℝ | a < x ∧ x < b} := by
      rw [h] at *
      exact h9
    simp at h10
    nlinarith

  have hb1 : b ≥ 5 := by
    by_contra h7
    push_neg at h7
    have h14 : b < 5 := by linarith
    have h9 : ((b + 5)/2 : ℝ) ∈ {x : ℝ | -4 < 2 * (x - 1) ∧ 2 * (x - 1) < 8} := by
      constructor
      ·
        -- Show $-4 < 2 * ((b + 5)/2 - 1)$
        have h10 : -4 < 2 * (((b + 5)/2 : ℝ) - 1) := by
          nlinarith
        linarith
      ·
        -- Show $2 * ((b + 5)/2 - 1) < 8$
        have h11 : 2 * (((b + 5)/2 : ℝ) - 1) < 8 := by
          nlinarith
        linarith
    have h10 : ((b + 5)/2 : ℝ) ∈ {x : ℝ | a < x ∧ x < b} := by
      rw [h] at *
      exact h9
    simp at h10
    nlinarith

  have ha2 : a ≥ -1 := by
    by_contra h7
    push_neg at h7
    have h15 : a < -1 := by linarith
    have h9 : ((a + -1)/2 : ℝ) ∈ {x : ℝ | a < x ∧ x < b} := by
      constructor
      ·
        nlinarith
      ·
        nlinarith
    have h10 : ((a + -1)/2 : ℝ) ∈ {x : ℝ | -4 < 2 * (x - 1) ∧ 2 * (x - 1) < 8} := by
      rw [h] at *
      exact h9
    simp at h10
    nlinarith

  have hb2 : b ≤ 5 := by
    by_contra h7
    push_neg at h7
    have h14 : b > 5 := by linarith
    have h9 : ((5 + b)/2 : ℝ) ∈ {x : ℝ | a < x ∧ x < b} := by
      constructor
      ·
        nlinarith
      ·
        nlinarith
    have h10 : ((5 + b)/2 : ℝ) ∈ {x : ℝ | -4 < 2 * (x - 1) ∧ 2 * (x - 1) < 8} := by
      rw [h] at *
      exact h9
    simp at h10
    nlinarith

  have ha3 : a = -1 := by linarith
  have hb3 : b = 5 := by linarith
  linarith [ha3, hb3]