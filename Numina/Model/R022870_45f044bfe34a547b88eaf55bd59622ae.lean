import Mathlib

open Real

theorem algebra_7038 (α : ℝ) :
    sin (3 * α) = 3 * sin α - 4 * sin α ^ 3 ∧
    cos (3 * α) = 4 * cos α ^ 3 - 3 * cos α ∧
    sin (4 * α) = 4 * sin α * cos α ^ 3 - 4 * sin α ^ 3 * cos α ∧
    cos (4 * α) = cos α ^ 4 - 6 * sin α ^ 2 * cos α ^ 2 + sin α ^ 4 ∧
    cos α ^ 4 = (cos (4 * α) + 4 * cos (2 * α) + 3) / 8 ∧
    sin α ^ 3 = -(sin (3 * α) - 3 * sin α) / 4 := by
  constructor
  · -- Proof of sin 3α = 3 sin α - 4 sin³ α
    rw [sin_three_mul]
    all_goals ring
  constructor
  · -- Proof of cos 3α = 4 cos³ α - 3 cos α
    rw [cos_three_mul]
    all_goals ring
  constructor
  · -- Proof of sin 4α = 4 sin α cos³ α - 4 sin³ α cos α
    have h1 : sin (4 * α) = 2 * sin (2 * α) * cos (2 * α) := by
      rw [show 4 * α = 2 * (2 * α) by ring]
      rw [sin_two_mul]
      <;> ring
    rw [h1]
    have h2 : sin (2 * α) = 2 * sin α * cos α := by
      rw [sin_two_mul]
      <;> ring
    have h3 : cos (2 * α) = cos α ^ 2 - sin α ^ 2 := by
      rw [cos_two_mul]
      rw [sin_sq]
      <;> ring
    rw [h2, h3]
    ring_nf
  constructor
  · -- Proof of cos 4α = cos⁴ α - 6 sin² α cos² α + sin⁴ α
    have h1 : cos (4 * α) = 2 * cos (2 * α) ^ 2 - 1 := by
      rw [show 4 * α = 2 * (2 * α) by ring]
      rw [cos_two_mul]
      all_goals ring
    rw [h1]
    have h2 : cos (2 * α) = 2 * cos α ^ 2 - 1 := by
      rw [cos_two_mul]
      all_goals nlinarith [Real.cos_sq_add_sin_sq α]
    rw [h2]
    have h3 : sin α ^ 2 = 1 - cos α ^ 2 := by
      have h : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
      linarith
    nlinarith [Real.sin_sq_add_cos_sq α, sq_nonneg (cos α ^ 2 - 1), sq_nonneg (sin α), sq_nonneg (cos α - 1)]
  constructor
  · -- Proof of cos⁴ α = (cos 4α + 4 cos 2α + 3) / 8
    have h1 : cos (4 * α) = 2 * cos (2 * α) ^ 2 - 1 := by
      rw [show 4 * α = 2 * (2 * α) by ring]
      rw [cos_two_mul]
      all_goals ring
    have h2 : cos (2 * α) = 2 * cos α ^ 2 - 1 := by
      rw [cos_two_mul]
      all_goals nlinarith [Real.cos_sq_add_sin_sq α]
    rw [h1, h2]
    have h3 : sin α ^ 2 = 1 - cos α ^ 2 := by
      have h : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
      linarith
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq α, sq_nonneg (cos α ^ 2 - 1), sq_nonneg (sin α), sq_nonneg (cos α - 1)]
  · -- Proof of sin³ α = -(sin 3α - 3 sin α) / 4
    have h1 : sin (3 * α) = 3 * sin α - 4 * sin α ^ 3 := by
      rw [sin_three_mul]
      all_goals ring
    linarith [h1]