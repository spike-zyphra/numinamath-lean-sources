import Mathlib

open Real Set
open scoped Real

theorem algebra_98173 (θ : Real) (hθ : θ ∈ Ioo 0 (π / 2)) (a : ℝ)
    (ha : sin (2 * θ) = a) :
    sin θ + cos θ = sqrt (a + 1) := by
  rcases hθ with ⟨h1, h2⟩
  have h3 : 0 < θ := h1
  have h4 : θ < π / 2 := h2
  have h5 : sin θ > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h3, Real.pi_pos]
    linarith [h4, Real.pi_pos]
  have h6 : cos θ > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [h3, Real.pi_pos]
    · linarith [h4, Real.pi_pos]
  have h7 : sin (2 * θ) = 2 * sin θ * cos θ := by
    rw [sin_two_mul]
  rw [h7] at ha
  have h8 : (sin θ + cos θ) ^ 2 = 1 + a := by
    calc
      (sin θ + cos θ) ^ 2 = sin θ ^ 2 + cos θ ^ 2 + 2 * (sin θ * cos θ) := by ring
      _ = (sin θ ^ 2 + cos θ ^ 2) + 2 * (sin θ * cos θ) := by ring
      _ = 1 + 2 * (sin θ * cos θ) := by
        have h9 : sin θ ^ 2 + cos θ ^ 2 = 1 := by
          exact Real.sin_sq_add_cos_sq θ
        rw [h9]
      _ = 1 + a := by
        have h10 : 2 * (sin θ * cos θ) = a := by
          linarith
        rw [h10]
  have h11 : sin θ + cos θ > 0 := by
    linarith [h5, h6]
  have h12 : sqrt ((sin θ + cos θ) ^ 2) = sin θ + cos θ := by
    rw [Real.sqrt_sq (show 0 ≤ (sin θ + cos θ) by linarith [h5, h6])]
  have h13 : sqrt ((sin θ + cos θ) ^ 2) = sqrt (a + 1) := by
    have h14 : (sin θ + cos θ) ^ 2 = 1 + a := h8
    have h15 : (sin θ + cos θ) ^ 2 = a + 1 := by
      linarith [h14]
    rw [h15]
    all_goals linarith
  have h16 : sin θ + cos θ = sqrt (a + 1) := by
    linarith [h12, h13]
  exact h16