import Mathlib

open Matrix Real

theorem calculus_22496 {k : ℝ} (hk : k > 0) (θ : ℝ) (h : θ ∈ Set.Ioo 0 π)
    (D R : Matrix (Fin 2) (Fin 2) ℝ)
    (hD : D = !![k, 0; 0, k]) (hR : R = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ])
    (hDR : D * R = !![-7, 1; -1, -7]) :
    k = 5 * Real.sqrt 2 := by

  -- First extract equations from matrix multiplication

  have h1 := congr_arg (fun M => M 0 0) hDR
  simp [hD, hR, mul_apply, Fin.sum_univ_two] at h1
  
  have h2 := congr_arg (fun M => M 0 1) hDR
  simp [hD, hR, mul_apply, Fin.sum_univ_two] at h2
  
  have h3 := congr_arg (fun M => M 1 0) hDR
  simp [hD, hR, mul_apply, Fin.sum_univ_two] at h3
  
  have h4 := congr_arg (fun M => M 1 1) hDR
  simp [hD, hR, mul_apply, Fin.sum_univ_two] at h4
  
  have eq1 : k * Real.cos θ = -7 := by
    nlinarith
  
  have eq2 : k * Real.sin θ = -1 := by
    nlinarith

  have h_eq4 : k ^ 2 = 50 := by
    have h_eq5 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    nlinarith [eq1, eq2, Real.cos_sq_add_sin_sq θ]

  have hk_eq : k = Real.sqrt 50 := by
    have h_pos : k > 0 := hk
    have : k ^ 2 = 50 := h_eq4
    have hk' : k = Real.sqrt 50 := by
      rw [← this]
      field_simp
    exact_mod_cast hk'

  have h_eq6 : Real.sqrt 50 = 5 * Real.sqrt 2 := by
    calc
      Real.sqrt 50 = Real.sqrt (5 ^ 2 * 2) := by norm_num
      _ = (Real.sqrt (5 ^ 2)) * Real.sqrt 2 := by rw [Real.sqrt_mul (by norm_num)]
      _ = (5 : ℝ) * Real.sqrt 2 := by
        rw [Real.sqrt_sq (by norm_num)]
        all_goals norm_num
  rw [h_eq6] at hk_eq
  exact_mod_cast hk_eq