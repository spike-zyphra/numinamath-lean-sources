import Mathlib

theorem algebra_166731 {α β : ℝ} (h : α ≠ β) (h1 : 3*α^2+7*α+4=0) (h2 : 3*β^2+7*β+4=0)
    (y1 y2 : ℝ) (hy1 : y1=α/(β-1)) (hy2 : y2=β/(α-1)) :
    21*y1^2-23*y1+6=0 ∧ 21*y2^2-23*y2+6=0 := by
  have hne : α - β ≠ 0 := sub_ne_zero_of_ne h
  have eqsum : α + β = -7 / 3 := by
    have eq1 : 3 * α^2 + 7 * α + 4 = 0 := h1
    have eq2 : 3 * β^2 + 7 * β + 4 = 0 := h2
    have eq3 : 3 * (α^2 - β^2) + 7 * (α - β) = 0 := by nlinarith
    have eq4 : (α - β) * (3 * (α + β) + 7) = 0 := by
      ring_nf at eq3 ⊢
      linarith
    cases' (mul_eq_zero.1 eq4) with hne' hne''
    · -- Contradiction: assume α = β, which is false
      exfalso
      exact h (by linarith)
    · -- Case where $3(\alpha + \beta) + 7 = 0$
      linarith
  have eqprod : α * β = 4 / 3 := by
    nlinarith [sq_pos_of_ne_zero hne, sq_nonneg (α - β), sq_nonneg (α + β)]
  constructor
  · -- First part: prove 21*y1^2-23*y1+6=0
    rw [hy1]
    have hne1 : β - 1 ≠ 0 := by
      by_contra h'
      have he : β = 1 := by linarith
      rw [he] at h2
      nlinarith
    field_simp [hne1]
    nlinarith [sq_pos_of_ne_zero hne, sq_nonneg (α - 1), sq_nonneg (β - 1), sq_nonneg (α * β), sq_nonneg (α + β), sq_nonneg (α - β)]
  · -- Second part: prove 21*y2^2-23*y2+6=0
    rw [hy2]
    have hne1 : α - 1 ≠ 0 := by
      by_contra h'
      have he : α = 1 := by linarith
      rw [he] at h1
      nlinarith
    field_simp [hne1]
    nlinarith [sq_pos_of_ne_zero hne, sq_nonneg (α - 1), sq_nonneg (β - 1), sq_nonneg (α * β), sq_nonneg (α + β), sq_nonneg (α - β)]