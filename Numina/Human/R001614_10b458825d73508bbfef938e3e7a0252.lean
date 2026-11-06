import Mathlib

open Real in
theorem inequalities_24843 (x₁ x₂ y₁ y₂ z₁ z₂ : ℝ) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (h₁ : x₁ * y₁ > z₁ ^ 2)
    (h₂ : x₂ * y₂ > z₂ ^ 2) : 8 / ((x₁ + x₂) * (y₁ + y₂) - (z₁ + z₂) ^ 2) ≤
    1 / (x₁ * y₁ - z₁ ^ 2) + 1 / (x₂ * y₂ - z₂ ^ 2) := by
  have hy₁ : y₁ > 0 := mul_lt_mul_iff_of_pos_left hx₁|>.1 <| by simp [lt_of_le_of_lt (by positivity) h₁] 
  have hy₂ : y₂ > 0 := mul_lt_mul_iff_of_pos_left hx₂ |>.1 <| by simp [lt_of_le_of_lt (by positivity) h₂]
  letI u₁ := √(x₁ * y₁) + z₁
  letI u₂ := √(x₂ * y₂) + z₂
  letI v₁ := √(x₁ * y₁) - z₁
  letI v₂ := √(x₂ * y₂) - z₂
  have hv₁ : v₁ > 0 := by
    simp only [gt_iff_lt, sub_pos, v₁]
    if hz₁ : z₁ ≥ 0 then exact lt_sqrt hz₁|>.2 h₁ else 
    exact lt_of_lt_of_le (lt_of_not_ge hz₁) <| by positivity
  have hv₂ : v₂ > 0 := by
    simp only [gt_iff_lt, sub_pos, v₂, v₁]
    exact if hz₂ : z₂ ≥ 0 then lt_sqrt hz₂ |>.2 h₂ else lt_of_lt_of_le (lt_of_not_ge hz₂) (by positivity)
  have huv₁ : u₁ * v₁ = x₁ * y₁ - z₁ ^ 2 := by simp only [u₁, v₁]; ring_nf; rw [sq_sqrt] ; positivity
  have hu₁ : u₁ > 0 := mul_lt_mul_iff_of_pos_right hv₁ |>.1 <| by simp [huv₁, sub_pos.mpr h₁]
  have huv₂ : u₂ * v₂ = x₂ * y₂ - z₂ ^ 2 := by
    simp only [u₂, v₂]
    ring_nf; rw [sq_sqrt]; positivity
  have hu₂ : u₂ > 0 := mul_lt_mul_iff_of_pos_right (a := v₂) hv₂ |>.1 <| by simp [huv₂,sub_pos.mpr h₂]

  have hmul : (x₁ + x₂) * (y₁ + y₂) - (z₁ + z₂) ^ 2 = (u₁ + u₂) * (v₁ + v₂) + (√(x₁ * y₂) - √(x₂ * y₁)) ^ 2 := by
    simp only [u₁, u₂, v₁, v₂, sub_eq_zero]
    ring_nf
    rw [sq_sqrt, sq_sqrt, sq_sqrt, sq_sqrt, ←sqrt_mul, ←sqrt_mul]
    · ring_nf
    all_goals positivity

  rw [←huv₁, ←huv₂, hmul]
  trans 8 / ((u₁ + u₂) * (v₁ + v₂))
  · gcongr
    simp only [le_add_iff_nonneg_right, v₁, u₁, v₂, u₂]
    positivity
  · exact sub_nonneg.1 <| by 
      field_simp; refine div_nonneg ?_ <| by positivity
      trans (u₁ * v₁ - u₂ * v₂) ^ 2 + v₁ * v₂ * (u₁ - u₂) ^ 2 + u₁ * u₂ * (v₁ - v₂) ^ 2 
      · positivity 
      · exact le_of_eq (by ring)