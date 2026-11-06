import Mathlib

open Real

theorem algebra_288780 {f : ℝ → ℝ} (hf : ∀ x > 0, f x = 2 * (sin (log x))^2 + cos (log (x^2)) - 5) :
    f π = -4 := by
  have h1 : f π = 2 * (sin (log π))^2 + cos (log (π^2)) - 5 := by
    apply hf
    exact Real.pi_pos
  rw [h1]
  have h2 : log (π^2) = 2 * log π := by
    simp [log_pow]
    <;> ring_nf
    <;> field_simp
  rw [h2]
  have h3 : cos (2 * log π) = 1 - 2 * (sin (log π))^2 := by
    have h4 : cos (2 * log π) = cos (2 * (log π)) := by ring_nf
    rw [h4]
    have h5 : cos (2 * (log π)) = 1 - 2 * (sin (log π))^2 := by
      rw [cos_two_mul]
      rw [sin_sq]
      <;> ring
    linarith
  rw [h3]
  all_goals
    nlinarith [Real.sin_sq_le_one (log π), Real.sin_sq_add_cos_sq (log π)]