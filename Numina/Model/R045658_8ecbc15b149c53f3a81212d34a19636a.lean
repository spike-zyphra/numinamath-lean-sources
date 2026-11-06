import Mathlib

open Real Set
open scoped Real

theorem algebra_207774 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = tan x ^ 2 - 4 * tan x - 12 / tan x + 9 / tan x ^ 2 - 3) :
  IsLeast {y | ∃ x ∈ Ioo (-π/2) 0, f x = y} (3 + 8 * sqrt 3) := by
  constructor
  · -- Show that 3 + 8 * sqrt 3 is in the image
    use - (Real.pi / 3)
    constructor
    · -- Show that -π/3 ∈ (-π/2, 0)
      have h1 : -Real.pi / 3 > -Real.pi / 2 := by
        linarith [Real.pi_pos]
      have h2 : -Real.pi / 3 < (0 : ℝ) := by
        linarith [Real.pi_pos]
      constructor <;> linarith
    · -- Show that f(-π/3) = 3 + 8 * sqrt 3
      rw [h₀]
      have htan : tan (- (Real.pi / 3)) = - Real.sqrt 3 := by
        have htan1 : tan (- (Real.pi / 3)) = - tan (Real.pi / 3) := by
          rw [show - (Real.pi / 3) = - (Real.pi / 3) by ring]
          rw [tan_neg]
        have htan2 : tan (Real.pi / 3) = Real.sqrt 3 := by
          exact tan_pi_div_three
        rw [htan1, htan2]
      rw [htan]
      field_simp
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  · -- Show that 3 + 8 * sqrt 3 is the minimum
    intro y hy
    rcases hy with ⟨x, hx, hx₁⟩
    rcases hx with ⟨hx1, hx2⟩
    rw [h₀] at hx₁
    have htan1 : tan x < 0 := by
      have hx11 : -π / 2 < x := hx1
      have hx12 : x < 0 := hx2
      have h1 : cos x > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        · linarith
        · linarith
      have h2 : sin x < 0 := by
        apply sin_neg_of_neg_of_neg_pi_lt
        all_goals linarith
      have htan2 : tan x = sin x / cos x := by
        rw [Real.tan_eq_sin_div_cos]
      rw [htan2]
      apply div_neg_of_neg_of_pos
      · exact h2
      · exact h1
    have h4 : tan x ^ 2 > 0 := by
      nlinarith
    have h5 : tan x ≠ 0 := by
      nlinarith
    have h6 : tan x ^ 2 - 4 * tan x - 12 / tan x + 9 / tan x ^ 2 - 3 ≥ 3 + 8 * Real.sqrt 3 := by
      have h1 : tan x < 0 := htan1
      have hx7 : (tan x : ℝ) < 0 := htan1
      have hx8 : tan x ≠ 0 := h5
      have h2 : tan x ^ 2 > 0 := h4
      have h3 : (tan x : ℝ) ^ 2 - 4 * tan x - 12 / tan x + 9 / tan x ^ 2 - 3 - (3 + 8 * Real.sqrt 3) ≥ 0 := by
        have eq : (tan x : ℝ) ^ 2 - 4 * tan x - 12 / tan x + 9 / tan x ^ 2 - 3 - (3 + 8 * Real.sqrt 3) =
            ( (tan x ) ^ 4 - 4 * (tan x ) ^ 3 - 12 * (tan x ) + 9 - 6 * (tan x ) ^ 2 -8 * Real.sqrt 3 * (tan x ) ^ 2 ) / ( (tan x ) ^ 2 ) := by
          field_simp [(show (tan x : ℝ) ≠ 0 by exact hx8)]
          <;> ring
        rw [eq]
        apply div_nonneg
        nlinarith [sq_nonneg ((tan x ) ^ 2 - 3 ), sq_nonneg (tan x + Real.sqrt 3 ), sq_nonneg (tan x -3 ), sq_nonneg (tan x * Real.sqrt 3 + 3 ), sq_nonneg ((tan x * (Real.sqrt 3 ) - 3 )), sq_nonneg ( tan x +3 + Real.sqrt 3 ), sq_nonneg (tan x -3 * Real.sqrt 3 ), sq_nonneg (tan x +3 ), sq_nonneg (tan x * Real.sqrt 3 - 3 ), sq_nonneg ((tan x ) ^ 2 ), sq_nonneg ( tan x ), sq_nonneg (tan x - Real.sqrt 3 * ( -1  ) ), sq_nonneg (tan x + Real.sqrt 3 ), mul_nonneg (Real.sqrt_nonneg 3 ) (Real.sqrt_nonneg 3 ), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num ), mul_nonneg (show (0 : ℝ ) ≤ 3 by norm_num ) (Real.sqrt_nonneg 3 ), Real.sqrt_pos.mpr (show (0 : ℝ ) < 3 by norm_num ) ]
        all_goals nlinarith
      linarith
    linarith