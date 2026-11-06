import Mathlib

open Real Set
open scoped Real

theorem algebra_100007 {θ : ℝ} (hθ : θ ∈ Ioo 0 (π/2)) (a : ℝ)
  (ha : a = sin (2*θ)) :
  sin θ + cos θ = sqrt (a + 1) := by
  rcases hθ with ⟨hθ1, hθ2⟩
  have h1 : sin θ > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hθ1, hθ2, Real.pi_pos]
    linarith [hθ1, hθ2, Real.pi_pos]
  have h2 : cos θ > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [hθ1, hθ2, Real.pi_pos]
  have h3 : sin θ + cos θ > 0 := by
    linarith [h1, h2]
  have h4 : sin (2 * θ) = 2 * sin θ * cos θ := by
    rw [sin_two_mul]
  have h5 : (sin θ + cos θ) ^ 2 = 1 + a := by
    have h5a : sin θ ^ 2 + cos θ ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq θ
    have h5b : a = 2 * sin θ * cos θ := by
      rw [ha]
      rw [h4]
      <;> ring_nf <;> nlinarith
    calc
      (sin θ + cos θ) ^ 2 = sin θ ^ 2 + cos θ ^ 2 + 2 * sin θ * cos θ := by
        ring
      _ = (sin θ ^ 2 + cos θ ^ 2) + 2 * sin θ * cos θ := by ring
      _ = 1 + 2 * sin θ * cos θ := by
        rw [h5a]
        <;> nlinarith
      _ = 1 + a := by
        rw [h5b]
        <;> ring_nf <;> nlinarith
  have h6 : sin θ + cos θ = Real.sqrt (1 + a) := by
    have h7 : (sin θ + cos θ) ^ 2 = 1 + a := h5
    have h8 : sin θ + cos θ ≥ 0 := by linarith [h3]
    have h9 : sin θ + cos θ = Real.sqrt ( (sin θ + cos θ) ^ 2 ) := by
      rw [Real.sqrt_sq (show sin θ + cos θ ≥ 0 by linarith)]
      <;> nlinarith
    rw [h9, h7]
    all_goals nlinarith
  rw [h6]
  rw [show 1 + a = a + 1 by ring]
  <;> ring_nf <;> nlinarith