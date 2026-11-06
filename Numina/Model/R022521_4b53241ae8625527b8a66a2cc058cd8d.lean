import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_308750 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
  (hxy : x * y = 1) :
  IsLeast {t | ∃ x y : ℝ, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 1 ∧ t = 1 / x ^ 4 + 1 / (4 * y ^ 4)} 1 := by
  constructor
  · -- Show that 1 is in the set.
    use (2 ^ (1 / 4 : ℝ)), (2 ^ (-1 / 4 : ℝ))
    constructor
    · -- Show x ≠ 0
      positivity
    constructor
    · -- Show y ≠ 0
      positivity
    constructor
    · -- Show x * y = 1
      have h1 : (2 : ℝ) ^ (1 / 4 : ℝ) * (2 : ℝ) ^ (-1 / 4 : ℝ) = 1 := by
        have h2 : (2 : ℝ) ^ (1 / 4 : ℝ) * (2 : ℝ) ^ (-1 / 4 : ℝ) = (2 : ℝ) ^ (1 / 4 + (-1 / 4) : ℝ) := by 
          rw [← Real.rpow_add]
          ring_nf
          all_goals norm_num
        rw [h2]
        norm_num
      linarith
    · -- Show 1 = 1 / x ^ 4 + 1 / (4 * y ^ 4)
      have h2x4 : ( (2 : ℝ) ^ (1 / 4 : ℝ) ) ^ 4 = (2 : ℝ) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      have h2y4 : ( (2 : ℝ) ^ (-1 / 4 : ℝ) ) ^ 4 = (2 : ℝ) ^ (-1 : ℝ) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num
      have h3 : 1 / ( (2 : ℝ) ^ (1 / 4 : ℝ) ) ^ 4 = 1 / 2 := by 
        rw [h2x4]
        all_goals norm_num
      have h4 : 1 / (4 * ( (2 : ℝ) ^ (-1 / 4 : ℝ) ) ^ 4 ) = 1 / 2 := by
        rw [h2y4]
        field_simp
        <;> norm_num 
        all_goals norm_num
      rw [h3, h4]
      all_goals norm_num 
  · -- Show 1 is the least element in the set
    intro t ht
    rcases ht with ⟨x, y, hx, hy, hxy, ht⟩
    have h1 : y = 1 / x := by 
      field_simp at hxy ⊢
      <;> nlinarith 
      all_goals linarith 
    have hx4_pos : x^4 >0 := by 
      have h1: x^2 >0 := by 
        apply sq_pos_of_ne_zero 
        exact hx
      nlinarith [sq_nonneg x]
    have ht' : t = 1 / x^4 + x^4 / 4 := by
      rw [ht]
      have eq2 : 1 / (4 * y^4) = x^4 / 4 := by 
        rw [show y = 1 / x by linarith [h1]]
        field_simp
        <;> ring_nf 
        <;> field_simp [hx4_pos]
        <;> nlinarith [sq_pos_of_ne_zero hx, hx4_pos]
      nlinarith [eq2, sq_nonneg (y^2), sq_nonneg (x^2)]
    have h2 : (1 / x^4 + x^4 / 4) -1 ≥0 := by 
      have h3 : (1 / x^4 + x^4 / 4 -1 ) = ( (x^4 - 2)^2 ) / (4 * x^4) := by 
        field_simp 
        <;> ring_nf 
      have h4 : ( (x^4 - 2)^2 ) / (4 * x^4) ≥0 := by
        apply div_nonneg 
        · -- Show that (x^4 -2)^2 ≥0
          positivity
        · -- Show that 4 * x^4 ≥0 
          nlinarith [hx4_pos, sq_nonneg x]
      linarith [h3, h4]
    linarith [ht', h2]