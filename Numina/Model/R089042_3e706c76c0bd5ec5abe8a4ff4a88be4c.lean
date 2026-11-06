import Mathlib

theorem algebra_327201 (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (h : Real.cos (3 * θ) / Real.cos θ = 1 / 3) :
    Real.sin (3 * θ) / Real.sin θ = 7 / 3 := by 
  rcases hθ with ⟨h1, h2⟩
  have hcos_ne_zero : Real.cos θ ≠ 0 := by
    have h1' : θ > 0 := h1
    have h2' : θ < Real.pi / 2 := h2
    have hcos_pos : Real.cos θ > 0 := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [h1']
      · linarith [Real.pi_pos, h2']
    have : Real.cos θ ≠ 0 := by nlinarith
    exact_mod_cast this
  
  have h_eq : Real.cos (3 * θ) = (1 / 3) * Real.cos θ := by
    field_simp [hcos_ne_zero] at h
    linarith
  
  have h1_eq : Real.cos (3 * θ) = 4 * (Real.cos θ)^3 - 3 * Real.cos θ := by
    rw [Real.cos_three_mul]
  
  rw [h1_eq] at h_eq
  
  have h2_eq : (Real.cos θ) ^ 2 = 5 / 6 := by
    have h3 : Real.cos θ * (12 * (Real.cos θ)^2 - 10) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- h4 : Real.cos θ = 0 is impossible
      exfalso
      exact hcos_ne_zero (by linarith)
    · -- h5 : 12 * (Real.cos θ)^2 - 10 = 0
      nlinarith
  have h_coeθ_pos : Real.cos θ > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [h1]
    · linarith [Real.pi_pos, h2]
  have hsin_pos : Real.sin θ > 0 := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith [h1]
      · linarith [Real.pi_pos, h2]

  have h_eq1 : (Real.sin θ) ^ 2 = 1 / 6 := by
    have h_eq : (Real.sin θ)^2 + (Real.cos θ)^2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [h2_eq] at h_eq
    nlinarith
  
  have h3 : Real.sin (3 * θ) = 3 * Real.sin θ - 4 * (Real.sin θ) ^ 3 := by
    rw [Real.sin_three_mul]

  have h_eq2 : Real.sin (3 * θ)/Real.sin θ = 3 - 4 * (Real.sin θ) ^ 2 := by
    have h : Real.sin θ ≠ 0 := by
      have hsin_pos' : Real.sin θ > 0 := hsin_pos
      nlinarith
    rw [h3]
    field_simp [h]
    <;> nlinarith [hsin_pos, h_eq1]

  rw [h_eq2]
  nlinarith [h_eq1]