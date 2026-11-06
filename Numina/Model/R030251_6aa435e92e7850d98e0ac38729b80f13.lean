import Mathlib

theorem algebra_202034 {k : ℝ} (x₁ x₂ : ℝ) (hx₁ : x₁^2 + k * x₁ + 4 = 0) (hx₂ : x₂^2 + k * x₂ + 4 = 0)
    (hne : x₁ ≠ x₂) : x₁^2 + x₂^2 > 8 := by 
  have h1 : (x₁ - x₂) * (x₁ + x₂ + k) = 0 := by 
    have h2 : x₁^2 + k * x₁ + 4 = 0 := hx₁ 
    have h3 : x₂^2 + k * x₂ + 4 = 0 := hx₂ 
    have h4 : x₁^2 + k * x₁ + 4 - (x₂^2 + k * x₂ + 4) = 0 := by linarith 
    ring_nf at h4 ⊢ 
    linarith 
  have h2 : x₁ + x₂ + k = 0 := by 
    apply_fun (fun y => y / (x₁ - x₂)) at h1 
    field_simp [(show x₁ - x₂ ≠ 0 by intro h; apply hne; linarith)] at h1 
    linarith 
  --从h2得k = -(x₁ + x₂)
  have hk : k = -(x₁ + x₂) := by linarith 
  --代入原方程得x₁ x₂的乘积为4
  have h5 : x₁ * x₂ = 4 := by 
    rw [hk] at hx₁ 
    nlinarith 
  --根据两个根不同，差的平方大于0
  have h6 : (x₁ - x₂) ^ 2 > 0 := by 
    apply sq_pos_of_ne_zero 
    intro h 
    apply hne 
    linarith 
  --展开平方后整理得要证明的结论
  nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂), h5]