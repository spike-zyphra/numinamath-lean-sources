import Mathlib

open Real Set
open scoped Real

theorem algebra_246571 (θ : ℝ) (hθ : θ ∈ Ioo 0 (π / 2)) (a : ℝ)
  (ha : sin (2 * θ) = a) :
  sin θ + cos θ = sqrt (a + 1) := by
  rcases hθ with ⟨h1, h2⟩
  have h3 : sin θ > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [h1, h2, Real.pi_pos]
  have h4 : cos θ > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    all_goals linarith [h1, h2, Real.pi_pos]
  have h5 : sin (2 * θ) = 2 * sin θ * cos θ := by
    rw [sin_two_mul]
  rw [h5] at ha
  have h8 : sin θ + cos θ > 0 := by
    linarith [h3, h4]
  have h9 : (sin θ + cos θ) ^ 2 = 1 + a := by
    calc 
      (sin θ + cos θ) ^ 2 = sin θ ^ 2 + cos θ ^ 2 + 2 * (sin θ * cos θ) := by ring
      _ = (sin θ ^ 2 + cos θ ^ 2) + 2 * (sin θ * cos θ) := by ring
      _ = 1 + 2 * (sin θ * cos θ) := by 
        have h6 : sin θ ^ 2 + cos θ ^ 2 = 1 := by
          exact Real.sin_sq_add_cos_sq θ
        rw [h6]
        <;> ring
      _ = 1 + a := by
        have h7 : sin θ * cos θ = a / 2 := by
          nlinarith
          <;> ring_nf at ha ⊢ <;> nlinarith
        rw [show sin θ * cos θ = a / 2 by linarith [h7]]
        <;> ring_nf <;> nlinarith
  have h9' : a ≥ 0 := by
    have h10 : 2 * sin θ * cos θ ≥ 0 := by 
      nlinarith [h3, h4]
    linarith [show a = 2 * sin θ * cos θ by linarith, h10]
  have h10 : sqrt ((sin θ + cos θ) ^ 2) = sin θ + cos θ := by
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    all_goals linarith [h8]
  have h11 : sqrt ((sin θ + cos θ) ^ 2) = sqrt (a + 1) := by
    rw [show (sin θ + cos θ) ^ 2 = 1 + a by linarith [h9]]
    <;> ring_nf <;> norm_num <;> ring_nf at * <;> norm_num at * <;> try tauto
    <;> try { 
      apply Real.sqrt_inj
      all_goals nlinarith
    }
  have h12 : sin θ + cos θ = sqrt (a + 1) := by
    linarith [h10, h11, h8, Real.sqrt_nonneg (a + 1), h9']
  exact h12