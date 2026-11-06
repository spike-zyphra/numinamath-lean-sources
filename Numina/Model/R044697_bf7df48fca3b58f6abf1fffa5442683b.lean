import Mathlib

theorem algebra_328032 (α β : ℝ) (h₁ : α ∈ Set.Ioo 0 (Real.pi / 2)) (h₂ : β ∈ Set.Ioo 0 (Real.pi / 2))
    (h₃ : Real.cos α = Real.sqrt 5 / 5) (h₄ : Real.cos β = Real.sqrt 10 / 10) :
    α + β = 3 * Real.pi / 4 := by 
  rcases h₁ with ⟨hα1, hα2⟩
  rcases h₂ with ⟨hβ1, hβ2⟩
  have h6 : Real.sin α > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have h7 : Real.sin β > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith
  have h8 : Real.sin α = 2 * Real.sqrt 5 / 5 := by
    have h9 : Real.sin α > 0 := h6
    have h10 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    rw [h₃] at h10
    have h11 : Real.sin α ^ 2 = 4 / 5 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by linarith)]
    have h12 : Real.sin α = Real.sqrt (4 / 5) := by
      have h13 : Real.sin α ≥ 0 := by linarith
      have h14 : Real.sin α = Real.sqrt (Real.sin α ^ 2) := by
        rw [Real.sqrt_sq (show 0 ≤ Real.sin α by linarith)]
      rw [h14, h11]
    rw [h12]
    have h13 : Real.sqrt (4 / 5 : ℝ) = 2 * Real.sqrt 5 / 5 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf 
      <;> norm_num [Real.sq_sqrt]
    linarith
  have h9 : Real.sin β = 3 * Real.sqrt 10 / 10 := by
    have h10 : Real.sin β > 0 := h7
    have h11 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
    rw [h₄] at h11
    have h12 : Real.sin β ^ 2 = 9 / 10 := by
      nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show 0 ≤ (10 : ℝ) by linarith)]
    have h13 : Real.sin β = Real.sqrt (9 / 10) := by
      have h14 : Real.sin β ≥ 0 := by linarith
      have h15 : Real.sin β = Real.sqrt (Real.sin β ^ 2) := by
        rw [Real.sqrt_sq (show 0 ≤ Real.sin β by linarith)]
      rw [h15, h12]
    rw [h13]
    have h14 : Real.sqrt (9 / 10 : ℝ) = 3 * Real.sqrt 10 / 10 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf 
      <;> norm_num [Real.sq_sqrt]
    linarith
  have h10 : Real.cos (α + β) = -Real.sqrt 2 / 2 := by
    rw [Real.cos_add]
    simp only [h₃, h₄, h8, h9]
    have h5 : Real.sqrt 5 * Real.sqrt 10 = 5 * Real.sqrt 2 := by
      calc
        Real.sqrt 5 * Real.sqrt 10 = Real.sqrt (5 * 10) := by rw [Real.sqrt_mul (by norm_num)]
        _ = Real.sqrt (50 : ℝ) := by norm_num
        _ = Real.sqrt (5^2 * 2) := by norm_num
        _ = (5 : ℝ) * Real.sqrt 2 := by
          rw [Real.sqrt_mul (by norm_num)]
          rw [Real.sqrt_sq (by norm_num)]
    have h2 : (Real.sqrt 5 / 5 : ℝ) * (Real.sqrt 10 / 10 : ℝ) = Real.sqrt 2 / 10 := by
      calc
        (Real.sqrt 5 / 5 : ℝ) * (Real.sqrt 10 / 10 : ℝ) 
          = (Real.sqrt 5 * Real.sqrt 10) / 50 := by ring
        _ = (5 * Real.sqrt 2) / 50 := by rw [h5]
        _ = Real.sqrt 2 / 10 := by ring
    have h3 : (2 * Real.sqrt 5 / 5 : ℝ) * (3 * Real.sqrt 10 / 10 : ℝ) = 3 * Real.sqrt 2 / 5 := by
      calc
        (2 * Real.sqrt 5 / 5 : ℝ) * (3 * Real.sqrt 10 / 10 : ℝ) 
          = 6 * (Real.sqrt 5 * Real.sqrt 10) / 50 := by ring
        _ = 6 * (5 * Real.sqrt 2) / 50 := by rw [h5]
        _ = 3 * Real.sqrt 2 / 5 := by ring
    linarith [h2, h3]
  have h11 : Real.cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
    have h12 : Real.cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
      have h9 : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
      rw [h9]
      rw [Real.cos_pi_sub]
      have h8 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      linarith
    exact h12
  have h12 : α + β = 3 * Real.pi / 4 := by 
    have h14 : Real.cos (α + β) = Real.cos (3 * Real.pi / 4) := by
      linarith [h10, h11]
    have h15 : α + β ≤ Real.pi := by 
      nlinarith [Real.pi_pos]
    have h16 : α + β ≥ 0 := by 
      nlinarith [Real.pi_pos]
    have h17 : 3 * Real.pi / 4 ≤ Real.pi := by
      nlinarith [Real.pi_pos]
    have h18 : 0 ≤ 3 * Real.pi / 4 := by 
      nlinarith [Real.pi_pos]
    have h20 : α + β = 3 * Real.pi / 4 := by
      have h23 : α + β ∈ Set.Icc (0 : ℝ) Real.pi := by 
        constructor
        · linarith
        · linarith [Real.pi_pos]
      have h24 : (3 * Real.pi / 4) ∈ Set.Icc (0 : ℝ) Real.pi := by 
        constructor
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      apply Real.injOn_cos h23 h24 (by linarith)
    exact h20
  exact h12