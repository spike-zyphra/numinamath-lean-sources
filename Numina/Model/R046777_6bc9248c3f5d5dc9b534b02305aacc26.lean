import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_156549 (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b > c) (h₂ : a + c > b) (h₃ : b + c > a) :
  a^2 < 2 * (b^2 + c^2) ∧
  ∀ ε > 0, ∃ a b c : ℝ,
    0 < a ∧ 0 < b ∧ 0 < c ∧
    a + b > c ∧ a + c > b ∧ b + c > a ∧
    |(a^2 - 2 * (b^2 + c^2))| < ε := by
  constructor
  · -- Proof of the first part
    have h₄ : 0 < a := h₀.1
    have h₅ : 0 < b := h₀.2.1
    have h₆ : 0 < c := h₀.2.2
    have h₇ : (b + c) ^ 2 > a ^ 2 := by
      have h₈ : a < b + c := by linarith
      nlinarith [mul_pos h₄ (show 0 < b + c by linarith), sq_pos_of_pos h₄, sq_pos_of_pos (show 0 < b + c by linarith)]
    have h₁₃ : (b + c) ^ 2 ≤ 2 * (b ^ 2 + c ^ 2) := by
      nlinarith [sq_nonneg (b - c)]
    nlinarith
  · -- Proof of the second part
    intro ε hε
    use (8 + ε) / (4 + ε), 1, 1
    constructor
    · -- Proof that 0 < a
      have h₁₈ : 0 < (8 + ε) / (4 + ε) := by
        apply div_pos
        all_goals linarith
      linarith
    constructor
    · -- Proof that 0 < b
      norm_num
    constructor
    · -- Proof that 0 < c
      norm_num
    constructor
    · -- Proof that a + b > c
      have h₁₈ : (8 + ε) / (4 + ε) + (1 : ℝ) > (1 : ℝ) := by
        have h₄ : (8 + ε) / (4 + ε) > 0 := by
          apply div_pos
          all_goals linarith
        linarith
      linarith
    constructor
    · -- Proof that a + c > b
      have h₁₈ : (8 + ε) / (4 + ε) + (1 : ℝ) > (1 : ℝ) := by
        have h₄ : (8 + ε) / (4 + ε) > 0 := by
          apply div_pos
          all_goals linarith
        linarith
      linarith
    constructor
    · -- Proof that b + c > a
      have h₄ : 1 + 1 > (8 + ε) / (4 + ε) := by
        have h₅ : (8 + ε) / (4 + ε) < 2 := by
          have h₆ : ε > 0 := hε
          have h₇ : 4 + ε > 0 := by linarith
          apply (div_lt_iff₀ (by linarith)).mpr
          nlinarith
        linarith
      linarith
    · -- Proof that |(a^2 - 2 * (b^2 + c^2))| < ε
      have h₈ : -ε < ((8 + ε) / (4 + ε)) ^ 2 - 2 * ((1: ℝ) ^ 2 + (1: ℝ) ^ 2) := by
        have h₆ : ε > 0 := hε
        have h₇ : 4 + ε > 0 := by linarith
        have h₈ : ((8 + ε) / (4 + ε)) ^ 2 - 2 * ((1: ℝ) ^ 2 + (1: ℝ) ^ 2) > -ε := by
          have h₃ : ((8 + ε) / (4 + ε)) ^ 2 - 2 * ((1: ℝ) ^ 2 + (1: ℝ) ^ 2) = ((8 + ε) ^ 2 - 4 * (4 + ε) ^ 2) / (4 + ε) ^ 2 := by
            field_simp
            <;> ring
          have h₇ : ((8 + ε) ^ 2 - 4 * (4 + ε) ^ 2 : ℝ) = -16 * ε - 3 * ε ^ 2 := by
            nlinarith
          rw [h₃, h₇]
          apply (lt_div_iff₀ (by positivity)).mpr
          nlinarith [sq_pos_of_pos (show ε > 0 by linarith), sq_nonneg (ε ^ 2)]
        linarith
      have h₉ : ((8 + ε) / (4 + ε)) ^ 2 - 2 * ((1: ℝ) ^ 2 + (1: ℝ) ^ 2) < ε := by
        have h₆ : ε > 0 := hε
        have h₇ : 4 + ε > 0 := by linarith
        have h₈ : ((8 + ε) / (4 + ε)) ^ 2 - 2 * ((1: ℝ) ^ 2 + (1: ℝ) ^ 2) < ε := by
          have h₃ : ((8 + ε) / (4 + ε)) ^ 2 - 2 * ((1: ℝ) ^ 2 + (1: ℝ) ^ 2) = ((8 + ε) ^ 2 - 4 * (4 + ε) ^ 2) / (4 + ε) ^ 2 := by
            field_simp
            <;> ring
          have h₇ : ((8 + ε) ^ 2 - 4 * (4 + ε) ^ 2 : ℝ) = -16 * ε - 3 * ε ^ 2 := by
            nlinarith
          rw [h₃, h₇]
          apply (div_lt_iff₀ (by positivity)).mpr
          nlinarith [sq_pos_of_pos (show ε > 0 by linarith), sq_nonneg (ε ^ 2)]
        linarith
      have h₂ : |((8 + ε) / (4 + ε)) ^ 2 - 2 * ((1: ℝ) ^ 2 + (1: ℝ) ^ 2)| < ε := by
        have h₃ : -ε < ((8 + ε) / (4 + ε)) ^ 2 - 2 * ((1: ℝ) ^ 2 + (1: ℝ) ^ 2) := h₈
        have h₄ : ((8 + ε) / (4 + ε)) ^ 2 - 2 * ((1: ℝ) ^ 2 + (1: ℝ) ^ 2) < ε := h₉
        apply abs_lt.mpr
        constructor <;> linarith
      simpa using h₂