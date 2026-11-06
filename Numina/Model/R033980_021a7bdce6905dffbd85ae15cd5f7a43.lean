import Mathlib

open Real Set
open scoped Real

theorem inequalities_213988 (a b c : ℝ) (α β γ : ℝ)
  (h₀ : α ∈ Ioo 0 (π/2)) (h₁ : β ∈ Ioo 0 (π/2)) (h₂ : γ = π/2)
  (h₃ : a > 0) (h₄ : b > 0) (h₅ : c > 0)
  (h₆ : a^2 + b^2 = c^2) -- 勾股定理
  (h₇ : sin α = a / c) (h₈ : sin β = b / c) -- 正弦定理应用
  (h₉ : cos α = b / c) (h₁₀ : cos β = a / c) -- 余弦定理应用
  (m_a m_b m_c : ℝ)
  (hm_a : m_a = b * sin γ) (hm_b : m_b = a * sin γ) (hm_c : m_c = (a * b) / c) :
  m_a / a + m_b / b + m_c / c ≥ 2 * cos α * cos β * cos γ * (1 / sin (2 * α) + 1 / sin (2 * β) + 1 / sin (2 * γ)) + sqrt 3 := by
  have h11 : cos γ = 0 := by
    rw [h₂]
    norm_num [cos_pi_div_two]
  have h12 : sin γ = 1 := by
    rw [h₂]
    norm_num [sin_pi_div_two]
  have h3 : sin (2 * γ) = 0 := by
    rw [h₂]
    have h4 : 2 * (π / 2) = π := by ring
    rw [h4]
    simp [sin_pi]
  have h13 : m_a = b * 1 := by
    rw [hm_a, h12]
    all_goals linarith
  have h14 : m_b = a * 1 := by
    rw [hm_b, h12]
    all_goals linarith
  have h15 : m_c = (a * b) / c := by
    exact_mod_cast hm_c
  have h16 : m_a / a + m_b / b + m_c / c = b / a + a / b + (a * b) / (c ^ 2) := by
    rw [h13, h14, h15]
    field_simp [h₃, h₄, h₅]
    <;> nlinarith [h₃, h₄, h₅, h₆]
  have h17 : 2 * cos α * cos β * cos γ * (1 / sin (2 * α) + 1 / sin (2 * β) + 1 / sin (2 * γ)) + sqrt 3 = sqrt 3 := by
    rw [h11]
    norm_num
    <;> field_simp [h3]
    <;> linarith
  rw [h16, h17]
  have h18 : b / a + a / b + (a * b) / (c ^ 2) ≥ sqrt 3 := by
    have h19 : b / a + a / b ≥ 2 := by
      have h4 : a > 0 := by linarith
      have h5 : b > 0 := by linarith
      have h6 : b / a + a / b - 2 ≥ 0 := by
        have h7 : b / a + a / b - 2 = (b - a) ^ 2 / (a * b) := by
          field_simp
          <;> ring
        rw [h7]
        have h8 : (b - a) ^ 2 ≥ 0 := by nlinarith
        have h9 : a * b > 0 := mul_pos (by linarith) (by linarith)
        positivity
      linarith
    have h21 : (a * b) / (c ^ 2) ≥ 0 := by
      apply div_nonneg
      nlinarith
      positivity
    have h24 : sqrt 3 > 0 := by positivity
    have h25 : sqrt 3 < (2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h23 : b / a + a / b + (a * b) / (c ^ 2) ≥ 2 := by
      linarith [h19, show (a * b) / (c ^ 2) ≥ 0 by positivity]
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  linarith