import Mathlib

open Real Set
open scoped Real

theorem algebra_115824 (α β : ℝ) (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2))
    (h₂ : α - β = π / 3) :
    sin α ^ 2 + cos β ^ 2 - sqrt 3 * sin α * cos β = 1 / 4 := by

  rcases h₀ with ⟨hα1, hα2⟩
  rcases h₁ with ⟨hβ1, hβ2⟩
  have h3 : α = β + π / 3 := by linarith
  have h4 : sin α = sin (β + π / 3) := by
    rw [h3]
  have h5 : sin (β + π / 3) = sin β * cos (π / 3) + cos β * sin (π / 3) := by
    rw [sin_add]
  have h6 : cos (π / 3) = 1 / 2 := by
    exact cos_pi_div_three
  have h7 : sin (π / 3) = Real.sqrt 3 / 2 := by
    exact sin_pi_div_three
  have h8 : sin α = (1 / 2) * sin β + (Real.sqrt 3 / 2) * cos β := by
    rw [h4, h5, h6, h7]
    <;> ring
  rw [h8]
  have h10 : Real.sqrt 3 ^ 2 = 3 := by
    exact Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
  have h11 : sin β ^ 2 + cos β ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq β
  nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, sq_nonneg (sin β - Real.sqrt 3 * cos β), sq_nonneg (cos β), sq_nonneg (sin β - cos β), Real.sin_pos_of_pos_of_lt_pi (show 0 < β by linarith) (show β < Real.pi by linarith [Real.pi_pos, hβ2]), Real.sin_sq_add_cos_sq β, mul_pos (show sin β > 0 by apply sin_pos_of_pos_of_lt_pi <;> linarith [hβ1, Real.pi_pos, hβ2, Real.pi_pos]) (show cos β > 0 by apply cos_pos_of_mem_Ioo <;> constructor <;> linarith [Real.pi_pos, hβ1, hβ2]), h10]