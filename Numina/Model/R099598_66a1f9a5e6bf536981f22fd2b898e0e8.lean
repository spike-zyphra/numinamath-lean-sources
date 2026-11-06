import Mathlib

open Real Set
open scoped Real

theorem algebra_4416 (θ : ℝ) (hθ : θ ∈ Ioo 0 (π / 2)) (h : 17 * sin θ ^ 2 + 13 * cos θ ^ 2 = 16) :
    θ = π / 3 := by
  rcases hθ with ⟨hθ1, hθ2⟩
  have h1 : sin θ ^ 2 + cos θ ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq θ
  have h2 : cos θ ^ 2 = 1 - sin θ ^ 2 := by
    linarith 
  rw [h2] at h
  have h3 : 4 * sin θ ^ 2 = 3 := by 
    linarith
  have h4 : sin θ > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals 
      linarith [Real.pi_pos, hθ1, hθ2]
  have h5 : sin θ ^ 2 = 3 / 4 := by
    linarith
  have h6 : sin θ = Real.sqrt (3 / 4) := by 
    have h7_pos : 0 ≤ sin θ := by linarith 
    have h8_eq : sin θ ^ 2 = (3 / 4 : ℝ) := by
      linarith 
    have h9 : sin θ = Real.sqrt (sin θ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg]
      linarith
    rw [h9, h8_eq]
    <;> ring_nf 
    <;> norm_num 
    <;> ring_nf 
    <;> norm_num
  have h7 : Real.sqrt (3 / 4 : ℝ) = Real.sqrt 3 / 2 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    <;> ring_nf 
    <;> norm_num 
  rw [h7] at h6
  have h8 : θ = Real.arcsin (sin θ) := by 
    rw [Real.arcsin_sin]
    all_goals 
      linarith [Real.pi_pos, hθ1, hθ2]
  have h9 : Real.arcsin (sin θ) = Real.arcsin (Real.sqrt 3 / 2) := by 
    rw [h6]
  have h10 : Real.arcsin (Real.sqrt 3 / 2) = π / 3 := by 
    have h11 : Real.sin (π / 3) = Real.sqrt 3 / 2 := by 
      exact sin_pi_div_three 
    rw [← h11]
    apply Real.arcsin_sin 
    all_goals 
      linarith [Real.pi_pos]
  rw [h8, h9, h10]
  <;> nlinarith
  <;> linarith [Real.pi_pos]
  <;> norm_num