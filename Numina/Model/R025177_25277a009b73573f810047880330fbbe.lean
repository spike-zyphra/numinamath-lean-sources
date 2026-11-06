import Mathlib


open Real Set


theorem algebra_310260 (α β : ℝ) (h₀ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₁ : β ∈ Set.Ioo 0 (Real.pi / 2))
    (h₂ : Real.sin α = x) (h₃ : Real.cos β = y) (h₄ : Real.cos (α + β) = -3 / 5) :
    y = -3 / 5 * Real.sqrt (1 - x ^ 2) + 4 / 5 * x ∧ 3 / 5 < x ∧ x < 1 := by
  rcases h₀ with ⟨h01, h02⟩
  rcases h₁ with  ⟨h11, h12⟩
  have h5 : Real.sin (α + β) > 0 := by
    have h8 : 0 < α + β := by nlinarith [h01, h11, Real.pi_pos]
    have h9 : α + β < Real.pi := by 
      nlinarith [h02, h12, Real.pi_pos]
    have h10 : Real.sin (α + β) > 0 := by
      apply Real.sin_pos_of_pos_of_lt_pi
      all_goals linarith
    linarith
  have h7 : Real.sin (α + β) = 4 / 5 := by
    have h8 : Real.sin (α + β) ^ 2 + Real.cos (α + β) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α + β)
    rw [show Real.cos (α + β) = -3 / 5 by linarith [h₄]] at h8
    nlinarith [h8, h5]
  have h8 : Real.sin α > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    all_goals
    linarith [h01, h02, Real.pi_pos]
  have h9 : Real.cos α > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    all_goals
    linarith [h01, h02, Real.pi_pos]
  have h10 : Real.sin β > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    all_goals
    linarith [h11, h12, Real.pi_pos]
  have h11 : Real.cos β > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    all_goals
    linarith [h11, h12, Real.pi_pos]
  have h12 : Real.cos α = Real.sqrt (1 - x ^ 2) := by
    have h13 : Real.cos α ^ 2 = 1 - x ^ 2 := by
      have h14 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
      rw [show Real.sin α = x by linarith [h₂]] at h14
      nlinarith
    have h14 : Real.cos α = Real.sqrt (1 - x^2) := by
      have h15 : Real.cos α ≥ 0 := by linarith
      have h17 : Real.cos α ^ 2 = 1 - x ^ 2 := h13
      have h18 : Real.cos α = Real.sqrt (1 - x ^ 2) := by
        rw [← h17]
        field_simp [Real.sqrt_sq (show 0 ≤ Real.cos α by linarith)]
      exact h18
    exact h14
  have eq1 : Real.cos (α + β) = Real.cos α * Real.cos β - Real.sin α * Real.sin β := by
    exact Real.cos_add α β
  have eq2 : Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by
    exact Real.sin_add α β
  rw [h₄] at eq1
  rw [h7] at eq2
  have eq3 : Real.cos α = Real.sqrt (1 - x ^ 2) := h12
  have eq4 : Real.sin α = x := by linarith [h₂]
  have eq5 : Real.cos β = y := by linarith [h₃]
  have eq7 : Real.sin β = Real.sqrt (1 - y^2) := by
    have h18 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
    rw [show Real.cos β = y by linarith [h₃]] at h18
    have h19 : Real.sin β ^ 2 = 1 - y^2 := by nlinarith
    have h20 : Real.sin β = Real.sqrt (1 - y^2) := by
      have h21 : Real.sin β ≥ 0 := by linarith
      have h22 : Real.sin β ^ 2 = 1 - y^2  := h19
      have h23 : Real.sin β = Real.sqrt (Real.sin β ^ 2) := by
        rw [Real.sqrt_sq (show 0 ≤ Real.sin β by linarith)]
      rw [h22] at h23
      linarith
    exact h20
  rw [eq3, eq5, eq4, eq7] at eq1 eq2
  have eq8 : y = -3 / 5 * Real.sqrt (1 - x ^ 2) + 4 / 5 * x := by
    have eq9 : Real.sqrt (1 - x ^ 2) * y - x * Real.sqrt (1 - y ^ 2) = -3 / 5 := by nlinarith [eq1]
    have eq10 : x * y + Real.sqrt (1 - x ^ 2) * Real.sqrt (1 - y ^ 2) = 4 / 5 := by nlinarith [eq2]
    have eq11 : 0 ≤ 1 - x ^ 2  := by
      have h13 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1  :=  Real.sin_sq_add_cos_sq α
      rw [show Real.sin α = x by linarith [h₂]] at h13
      nlinarith [sq_nonneg (Real.sin α ^ 2 - 1)]
    have eq12 : 0 ≤ 1 - y ^ 2  :=  by
      have h13 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1  :=  Real.sin_sq_add_cos_sq β
      rw [show Real.cos β = y by  linarith [h₃]] at h13
      nlinarith [sq_nonneg (Real.sin β ^ 2 - 1)]
    nlinarith [Real.sqrt_nonneg (1 - x^2), Real.sqrt_nonneg (1 - y^2), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x ^ 2 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - y ^ 2 by linarith), sq_nonneg (y ^ 2 - 1), sq_nonneg (x ^ 2 - 1)]
  have h61 : 3 / 5 < x  :=  by
    have eq81 : y > 0  :=  by  nlinarith [h11, h₃]
    nlinarith [Real.sqrt_nonneg (1 - x^2), Real.sq_sqrt (show 0 ≤ 1 - x ^ 2  by
      have h13 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1  :=  Real.sin_sq_add_cos_sq α
      rw [show Real.sin α = x by  linarith [h₂]] at h13
      nlinarith [sq_nonneg (Real.sin α ^ 2 - 1)]
    ), sq_nonneg (y ^ 2 - 16 / 25), sq_nonneg (x ^ 2 - 9 / 25)]
  have h62 : x < 1  :=  by
    have h71 : Real.sin α < 1  :=  by
      have h72 : Real.sin α < Real.sin (Real.pi / 2)  :=  by
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals
        linarith [h01, h02, Real.pi_pos]
      have h73 : Real.sin (Real.pi / 2)  =  1  :=  Real.sin_pi_div_two
      nlinarith [h73, h72]
    nlinarith [h₂, h71]
  constructor
  · linarith [eq8]
  constructor
  · linarith [h61]
  · linarith [h62]