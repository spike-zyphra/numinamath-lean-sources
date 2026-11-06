import Mathlib

open BigOperators Real Set


lemma lemma_1 {x y : ℝ} (hx : x ∈ Set.Ioo (-2) 2) (hy : y ∈ Set.Ioo (-2) 2)
    (hxy : x * y = -1) : x ^ 2 ∈ Set.Ioo (1 / 4) 4 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have h1 : -2 < x := hx1
  have h2 : x < 2 := hx2
  have h3 : -2 < y := hy1
  have h4 : y < 2 := hy2
  have h22 : x ≠ 0 := by
    by_contra h
    rw [h] at hxy
    nlinarith
  constructor
  ·
    nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by exact h22), sq_nonneg (y + 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 2)]
  ·
    nlinarith


theorem algebra_9988 (x y : ℝ) (hx : x ∈ Ioo (-2) 2) (hy : y ∈ Ioo (-2) 2)
    (hxy : x * y = -1) :
    IsLeast {u | ∃ x y : ℝ, x ∈ Ioo (-2) 2 ∧ y ∈ Ioo (-2) 2 ∧ x * y = -1 ∧ u = 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2)} (12 / 5) := by
  constructor
  · -- Show that 12/5 is in the set
    use Real.sqrt (2 / 3), -Real.sqrt (3 / 2)
    constructor
    · -- Show sqrt(2/3) ∈ (-2, 2)
      have h2 : Real.sqrt (2 / 3) < 2 := by
        nlinarith [Real.sqrt_nonneg (2 / 3), Real.sq_sqrt (show 0 ≤ 2 / 3 by norm_num)]
      have h1 : -2 < Real.sqrt (2 / 3) := by
        have h1 : 0 < Real.sqrt (2 / 3) := by
          apply Real.sqrt_pos.mpr
          norm_num
        nlinarith [Real.sqrt_nonneg (2 / 3)]
      exact ⟨h1, h2⟩
    constructor
    · -- Show -sqrt(3/2) ∈ (-2, 2)
      have h3 : -2 < -Real.sqrt (3 / 2) := by
        have h4 : Real.sqrt (3 / 2) < 2 := by
          nlinarith [Real.sqrt_nonneg (3 / 2), Real.sq_sqrt (show 0 ≤ 3 / 2 by norm_num)]
        nlinarith [Real.sqrt_nonneg (3 / 2)]
      have h4 : -Real.sqrt (3 / 2) < 2 := by
        have h5 : 0 < Real.sqrt (3 / 2) := by
          apply Real.sqrt_pos.mpr
          norm_num
        nlinarith [Real.sqrt_nonneg (3 / 2)]
      exact ⟨h3, h4⟩
    constructor
    · -- Show sqrt(2/3) * (-sqrt(3/2)) = -1
      have h5 : Real.sqrt (2 / 3) * (-Real.sqrt (3 / 2)) = -1 := by
        have h6 : Real.sqrt (2 / 3) * Real.sqrt (3 / 2) = 1 := by
          have h7 : Real.sqrt (2 / 3) * Real.sqrt (3 / 2) = Real.sqrt ((2 / 3) * (3 / 2)) := by
            rw [← Real.sqrt_mul (by norm_num)]
          rw [h7]
          have h8 : (2 / 3 : ℝ) * (3 / 2 : ℝ) = (1 : ℝ) := by
            norm_num
          rw [h8]
          simp
        nlinarith
      linarith
    · -- Show 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) = 12 / 5
      have hx2 : Real.sqrt (2 / 3) ^ 2 = (2 / 3 : ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      have hy2 : (-Real.sqrt (3 / 2) : ℝ) ^ 2 = (3 / 2 : ℝ) := by
        have h6 : (Real.sqrt (3 / 2) : ℝ) ^ 2 = (3 / 2 : ℝ) := by
          rw [Real.sq_sqrt]
          norm_num
        nlinarith [show 0 ≤ (3 / 2 : ℝ) by norm_num]
      field_simp [hx2, hy2]
      <;> norm_num
  · -- Show that 12/5 is the least
    rintro u ⟨x, y, hx, hy, hxy, heq⟩
    have hx1 : -2 < x := by
      rcases hx with ⟨hx1, hx2⟩
      nlinarith
    have hx2 : x < 2 := by
      rcases hx with ⟨hx1, hx2⟩
      nlinarith
    have hy1 : -2 < y := by
      rcases hy with ⟨hy1, hy2⟩
      nlinarith
    have hy2 : y < 2 := by
      rcases hy with ⟨hy1, hy2⟩
      nlinarith
    have h1 : 0 < (4 - x ^ 2) := by
      nlinarith [sq_nonneg x]
    have h2 : 0 < (9 - y ^ 2) := by
      nlinarith [sq_nonneg y]
    have heq' : 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) ≥ 12 / 5 := by
      have h4 : 0 < (4 - x ^ 2) * (9 - y ^ 2) := by
        positivity
      have h5 : (4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) - 12 / 5) ≥ 0 := by
        have h7 : (4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) - 12 / 5) = (4 * (9 - y ^ 2) + 9 * (4 - x ^ 2) - (12 / 5) * (4 - x ^ 2) * (9 - y ^ 2)) / ((4 - x ^ 2) * (9 - y ^ 2)) := by
          field_simp
          ring
        rw [h7]
        have h7 : 4 * (9 - y ^ 2) + 9 * (4 - x ^ 2) - (12 / 5) * (4 - x ^ 2) * (9 - y ^ 2) ≥ 0 := by
          nlinarith [sq_nonneg (x ^ 2 - 2 / 3), sq_nonneg (y ^ 2 - 3 / 2), sq_nonneg (x * y + 1), sq_nonneg (x ^ 2 - 2 / 3), sq_nonneg (y ^ 2 - 3 / 2), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg ((x * y) + 1), mul_pos (show 0 < (4 - x ^ 2) by nlinarith) (show 0 < (9 - y ^ 2) by nlinarith)
          ]
        have h8 : 0 < (4 - x ^ 2) * (9 - y ^ 2) := by
          positivity
        positivity
      linarith
    linarith [heq, heq']