import Mathlib

open Real Set
open scoped Real

theorem calculus_22199 (θ : ℝ) (hθ : θ ∈ Ioo 0 (π/2)) (h : sqrt 3 * cos θ - sin θ = 1/3) :
    sqrt 3 * sin θ + cos θ = sqrt 35 / 3 := by
  rcases hθ with ⟨hθ1, hθ2⟩
  have h1 : cos θ > 0 := by
    apply cos_pos_of_mem_Ioo 
    constructor 
    · linarith [pi_pos]
    · linarith [pi_pos]
  have h2 : sin θ > 0 := by 
    apply sin_pos_of_pos_of_lt_pi 
    linarith [pi_pos] 
    linarith [pi_pos]
  have eq1 : (sqrt 3 * cos θ - sin θ) ^ 2 = (1/3) ^2 := by
    rw [h] 
  have eq2 : (sqrt 3 * cos θ - sin θ) ^ 2 = 3 * cos θ ^2 + sin θ ^2 - 2 * sqrt 3 * cos θ * sin θ := by 
    calc 
      (sqrt 3 * cos θ - sin θ) ^ 2
          = (sqrt 3 * cos θ - sin θ) ^ 2 := by rfl 
      _ = (sqrt 3 * cos θ) ^ 2 - 2 * (sqrt 3 * cos θ) * sin θ + sin θ ^2 := by ring 
      _ = (sqrt 3) ^2 * (cos θ) ^2 - 2 * sqrt 3 * cos θ * sin θ + sin θ ^2 := by ring_nf 
      _ = 3 * cos θ ^2 - 2 * sqrt 3 * cos θ * sin θ + sin θ ^2 := by 
        have h3 : (sqrt 3 : ℝ) ^2 = 3 := by 
          rw [Real.sq_sqrt]
          linarith 
        rw [h3]
        all_goals ring 
      _ = 3 * cos θ ^2 + sin θ ^2 - 2 * sqrt 3 * cos θ * sin θ := by ring 
  have eq3 : 3 * cos θ ^2 + sin θ ^2 - 2 * sqrt 3 * cos θ * sin θ = (1/3) ^2 := by 
    linarith [eq1, eq2]
  have eq4 : 3 * cos θ ^2 + sin θ ^2 - 2 * sqrt 3 * cos θ * sin θ = 1 / 9 := by 
    norm_num at eq3 ⊢ 
    linarith [eq3]
  have h3 : cos θ ^2 + sin θ ^2 = 1 := by 
    exact Real.cos_sq_add_sin_sq θ 
  have eq5 : (sqrt 3 * sin θ + cos θ )^2 = 35 / 9 := by 
    have eq6 : (sqrt 3 * sin θ + cos θ ) ^ 2 = 3 * sin θ ^2 + cos θ ^2 + 2 * sqrt 3 * sin θ * cos θ := by 
      calc 
        (sqrt 3 * sin θ + cos θ ) ^ 2 
          = (sqrt 3 * sin θ + cos θ ) ^ 2 := by rfl 
        _ = (sqrt 3 * sin θ) ^ 2 + (cos θ) ^2 + 2 * (sqrt 3 * sin θ) * (cos θ) := by ring 
        _ = 3 * sin θ ^2 + cos θ ^2 + 2 * sqrt 3 * sin θ * cos θ := by 
          have h7 : (sqrt 3 * sin θ) ^ 2 = 3 * sin θ ^2 := by 
            calc 
              (sqrt 3 * sin θ) ^ 2 = (sqrt 3) ^2 * (sin θ) ^2 := by ring 
              _ = 3 * (sin θ) ^2 := by 
                have h8 : (sqrt 3 : ℝ) ^2 = 3 := by 
                  rw [Real.sq_sqrt]
                  linarith 
                rw [h8] 
          rw [h7]
          all_goals ring 
    have eq9 : 3 * sin θ ^2 + cos θ ^2 + 2 * sqrt 3 * sin θ * cos θ = 35 / 9 := by 
      have eq10 : 3 * cos θ ^2 + sin θ ^2 - 2 * sqrt 3 * cos θ * sin θ = 1 / 9 := eq4 
      have h3' : cos θ ^2 + sin θ ^2 = 1 := h3 
      nlinarith [sq_nonneg (cos θ ^2 - 1 / 2), sq_nonneg (sin θ ^2 - 3 / 8), sq_nonneg (cos θ - sin θ), sq_nonneg (cos θ + sin θ), sq_pos_of_pos (show sin θ > 0 by linarith), sq_pos_of_pos (show cos θ > 0 by linarith)]
    linarith [eq6, eq9]
  have h4 : sqrt 3 * sin θ + cos θ > 0 := by 
    have h5 : sin θ > 0 := h2 
    have h6 : cos θ > 0 := h1 
    nlinarith [show sqrt 3 > 0 by positivity] 
  have eq7 : sqrt 3 * sin θ + cos θ = Real.sqrt (35 / 9) := by 
    have h8 : sqrt 3 * sin θ + cos θ > 0 := h4 
    have h9 : (sqrt 3 * sin θ + cos θ )^2 = 35 / 9 := eq5 
    have h10 : sqrt 3 * sin θ + cos θ = Real.sqrt (35 / 9) := by 
      have h11 : Real.sqrt ((sqrt 3 * sin θ + cos θ )^2) = Real.sqrt (35 / 9) := by 
        rw [h9] 
      have h12 : Real.sqrt ((sqrt 3 * sin θ + cos θ )^2) = sqrt 3 * sin θ + cos θ := by 
        rw [Real.sqrt_sq (by linarith)]
      linarith 
    linarith 
  have h9 : Real.sqrt (35 / 9) = Real.sqrt 35 / 3 := by 
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num 
    <;> ring_nf 
    <;> norm_num 
  rw [h9] at eq7 
  linarith [eq7]