import Mathlib

open Real Set
open scoped Real

theorem algebra_229100 (α β : ℝ) (h₀ : sin α + sin (α + β) + cos (α + β) = sqrt 3)
    (h₁ : β ∈ Icc (π / 4) π) :
    β = π / 4 := by
  rcases h₁ with ⟨h₁₁, h₁₂⟩
  have h2 : sin (α + β) = sin α * cos β + cos α * sin β := by 
    rw [sin_add]
  have h3 : cos (α + β) = cos α * cos β - sin α * sin β := by 
    rw [cos_add]
  rw [h2] at h₀
  rw [h3] at h₀
  have eq1 : sin α * (1 + cos β - sin β) + cos α * (sin β + cos β) = sqrt 3 := by
    linarith 
  have h8 : (sin α * (1 + cos β - sin β) + cos α * (sin β + cos β)) ^ 2 = 3 := by
    calc
      (sin α * (1 + cos β - sin β) + cos α * (sin β + cos β)) ^ 2 = (sqrt 3) ^ 2 := by
        rw [eq1]
      _ = 3 := by
        norm_num
  have h5 : (1 + cos β - sin β) ^ 2 + (sin β + cos β) ^ 2 ≥ 3 := by 
    have h10 : (sin α * (1 + cos β - sin β) + cos α * (sin β + cos β)) ^ 2 ≤ ( (1 + cos β - sin β) ^ 2 + (sin β + cos β) ^ 2 ) * (sin α ^2 + cos α ^2) := by
      nlinarith [sq_nonneg (sin α * (sin β + cos β) - cos α * (1 + cos β - sin β)), sq_nonneg (sin α * (1 + cos β - sin β) - cos α * (sin β + cos β)), sq_nonneg (sin α ^ 2 - cos α ^ 2), sq_nonneg ((1 + cos β - sin β) * sin α - (sin β + cos β) * cos α), sq_nonneg ((1 + cos β - sin β) * cos α - (sin β + cos β) * sin α), Real.sin_sq_add_cos_sq α]
    have h11 : sin α ^ 2 + cos α ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq α
    rw [h11] at h10 
    nlinarith [h8]
  have h7 : cos β ≥ sin β := by
    nlinarith [h5, Real.sin_sq_add_cos_sq β, Real.sin_sq_add_cos_sq β]
  have h15 : β ≤ π / 4 := by 
    by_contra h
    push_neg at h 
    have h2 : sin β > cos β := by
      have h3 : β > π / 4 := by linarith 
      have h4 : β - π / 4 > 0 := by linarith 
      have h5 : sin β = sin (π / 4 + (β - π / 4)) := by ring_nf 
      have h6 : cos β = cos (π / 4 + (β - π / 4)) := by ring_nf 
      have h7 : sin (π / 4 + (β - π / 4)) = (Real.sqrt 2 / 2) * (cos (β - π / 4) + sin (β - π / 4)) := by
        rw [sin_add]
        have h8 : sin (π / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four 
        have h9 : cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four 
        rw [h8, h9]
        <;> ring_nf <;> norm_num 
        <;> try ring_nf 
        <;> try linarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h8 : cos (π / 4 + (β - π / 4)) = (Real.sqrt 2 / 2) * (cos (β - π / 4) - sin (β - π / 4)) := by 
        rw [cos_add]
        have h9 : sin (π / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four 
        have h10 : cos (π / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four 
        rw [h9, h10]
        <;> ring_nf <;> norm_num 
        <;> try ring_nf 
        <;> try linarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      rw [h5, h6, h7, h8]
      have h9 : sin (β - π / 4) > 0 := by 
        apply sin_pos_of_pos_of_lt_pi 
        · linarith 
        · linarith [Real.pi_gt_three, h₁₂] 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sin_sq_add_cos_sq (β - π / 4)]
    linarith 
  linarith
  all_goals linarith
  all_goals linarith
  all_goals linarith
  all_goals linarith
  all_goals linarith
  all_goals linarith
  all_goals linarith