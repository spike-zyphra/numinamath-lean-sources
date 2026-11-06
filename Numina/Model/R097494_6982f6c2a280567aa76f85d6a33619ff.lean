import Mathlib

theorem algebra_104308 (α : ℝ) (h₀ : α ∈ Set.Ioo 0 (Real.pi)) (h₁ : Real.sin α - Real.cos α = 1 / 5) :
    Real.tan α = 4 / 3 := by
  rcases h₀ with ⟨hα₁, hα₂⟩
  have h2 : 0 < Real.sin α := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h3 : Real.sin α = Real.cos α + 1 / 5 := by
    linarith [h₁]
  have h4 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  rw [h3] at h4
  have h5 : 50 * Real.cos α ^ 2 + 10 * Real.cos α - 24 = 0 := by
    ring_nf at h4
    nlinarith
  have h6 : (Real.cos α - 3 / 5) * (50 * Real.cos α + 40) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- Case where Real.cos α - 3 / 5 = 0
    have hcos : Real.cos α = 3 / 5 := by linarith
    have hsin : Real.sin α = 4 / 5 := by
      linarith [h3, hcos]
    rw [Real.tan_eq_sin_div_cos]
    rw [hsin, hcos]
    norm_num
  · -- Case where 50 * Real.cos α + 40 = 0
    have hcos : Real.cos α = -4 / 5 := by linarith
    have hsin : Real.sin α = -3 / 5 := by
      linarith [h3, hcos]
    linarith -- contradicts h2 : 0 < Real.sin α