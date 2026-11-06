import Mathlib

open Real Set
open scoped Real

theorem algebra_11328 {α β : ℝ} (hα : α ∈ Ioo 0 Real.pi) (hβ : β ∈ Ioo 0 Real.pi)
    (hcosα : cos α + cos β = 3 / 5) (hcosαβ : cos α * cos β = -1 / 5) :
    sin α * sin β = sqrt 7 / 5 := by
  have h1 : 0 < α := hα.left
  have h2 : α < Real.pi := hα.right
  have h3 : 0 < β := hβ.left
  have h4 : β < Real.pi := hβ.right
  have hsinα_pos : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [Real.pi_pos]
  have hsinβ_pos : sin β > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [Real.pi_pos]
  have hcos_sq : cos α ^ 2 + cos β ^ 2 = 19 / 25 := by
    have h : cos α ^ 2 + cos β ^ 2 = (cos α + cos β)^2 - 2 * (cos α * cos β) := by
      ring
    rw [h, hcosα, hcosαβ]
    norm_num
  have hsin_sq : (sin α) ^ 2 * (sin β) ^ 2 = 7 / 25 := by
    have hsin2α : sin α ^ 2 = 1 - cos α ^ 2 := by
      have h : sin α ^ 2 + cos α ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq α
      linarith
    have hsin2β : sin β ^ 2 = 1 - cos β ^ 2 := by
      have h : sin β ^ 2 + cos β ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq β
      linarith
    calc
      (sin α) ^ 2 * (sin β) ^ 2 = (1 - cos α ^ 2) * (1 - cos β ^ 2) := by rw [hsin2α, hsin2β]
      _ = 1 - cos α ^ 2 - cos β ^ 2 + (cos α * cos β) ^ 2 := by ring
      _ = 1 - (cos α ^ 2 + cos β ^ 2) + (cos α * cos β) ^ 2 := by ring
      _ = 1 - (19 / 25) + (-1 / 5) ^ 2 := by rw [hcos_sq, hcosαβ]
      _ = 1 - (19 / 25) + (1 / 25) := by norm_num
      _ = 7 / 25 := by norm_num
  have hprod_pos : sin α * sin β > 0 := by
    apply mul_pos
    all_goals linarith
  have hsq : (sin α * sin β) ^ 2 = 7 / 25 := by
    calc 
      (sin α * sin β) ^ 2 = (sin α) ^ 2 * (sin β) ^ 2 := by ring
      _ = 7 / 25 := hsin_sq
  have h7 : sin α * sin β = Real.sqrt (7 / 25) := by
    have h2 : Real.sqrt ((sin α * sin β) ^ 2) = Real.sqrt (7 / 25) := by 
      rw [hsq]
    have h1 : Real.sqrt ((sin α * sin β) ^ 2) = sin α * sin β := by
      rw [Real.sqrt_sq (by linarith)]
    linarith [h1, h2]
  rw [h7]
  have : Real.sqrt (7 / 25) = Real.sqrt 7 / 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  exact this