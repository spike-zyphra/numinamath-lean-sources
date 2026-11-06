import Mathlib

theorem algebra_307980 (α β : ℝ) (h₀ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₁ : β ∈ Set.Ioo (-Real.pi / 2) 0)
    (h₂ : Real.sin β = -5 / 13) (h₃ : Real.sqrt ((Real.cos α - Real.cos β)^2 + (Real.sin α - Real.sin β)^2) = 2 * Real.sqrt 5 / 5) :
    Real.sin α = 33 / 65 := by
  rcases h₀ with ⟨hα1, hα2⟩
  rcases h₁ with ⟨hβ1, hβ2⟩

  have h4 : (Real.cos α - Real.cos β)^2 + (Real.sin α - Real.sin β)^2 = 4 / 5 := by
    calc
      (Real.cos α - Real.cos β) ^ 2 + (Real.sin α - Real.sin β) ^ 2 = (Real.sqrt ((Real.cos α - Real.cos β)^2 + (Real.sin α - Real.sin β)^2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = (2 * Real.sqrt 5 / 5) ^ 2 := by rw [h₃]
      _ = 4 * (Real.sqrt 5) ^ 2 / 25 := by ring_nf
      _ = 4 * 5 / 25 := by rw [Real.sq_sqrt]; all_goals linarith
      _ = 4 / 5 := by norm_num

  have h5 : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  have h6 : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β

  have h7 : Real.cos β > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · -- $-\pi/2 < \beta$
      linarith [hβ1, Real.pi_pos]
    · -- $\beta < 0$
      linarith [hβ2, Real.pi_pos]

  have h8 : Real.cos β = 12 / 13 := by
    have h9 : Real.cos β ^ 2 + Real.sin β ^ 2 = 1 := Real.cos_sq_add_sin_sq β
    rw [h₂] at h9
    nlinarith [h7]

  have h10 : Real.cos α * Real.cos β + Real.sin α * Real.sin β = 3 / 5 := by
    nlinarith [h5, h6, h4]

  have h11 : Real.sin α > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [hα1, hα2, Real.pi_pos]
    linarith [hα1, hα2, Real.pi_pos]

  have h12 : Real.sin (α - β) > 0 := by
    have h15 : 0 < α - β := by
      nlinarith [hα1, hβ2, Real.pi_pos]
    have h16 : α - β < Real.pi := by
      nlinarith [hα2, hβ1, Real.pi_pos]
    have h17 : 0 < Real.sin (α - β) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      all_goals linarith [h15, h16, Real.pi_pos]
    linarith

  have h13 : Real.sin (α - β) = 4 / 5 := by
    have h18 : Real.sin (α - β) ^ 2 + Real.cos (α - β) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α - β)
    have h19 : Real.cos (α - β) = 3 / 5 := by
      rw [Real.cos_sub]
      nlinarith
    rw [h19] at h18
    have h20 : Real.sin (α - β) > 0 := h12
    nlinarith [h20]

  have h14 : Real.sin α = Real.sin β * Real.cos (α - β) + Real.cos β * Real.sin (α - β) := by
    have h16 : Real.sin α = Real.sin (β + (α - β)) := by ring_nf
    rw [h16]
    rw [Real.sin_add]
    all_goals ring_nf

  have hcos1 : Real.cos (α - β) = 3 / 5 := by
    rw [Real.cos_sub]
    nlinarith

  rw [h14]
  rw [hcos1, h13, h8, h₂]
  field_simp at *
  <;> nlinarith [Real.pi_pos, hα1, hα2, hβ1, hβ2]