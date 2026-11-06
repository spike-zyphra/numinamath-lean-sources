import Mathlib

theorem algebra_10223 {u : ℝ → ℝ} (hu : ∀ x, u x = -x + 3 * Real.sin (x * Real.pi / 3)) :
    u (-2.33) + u (-0.81) + u (0.81) + u (2.33) = 0 := by
  have h1 : u (-2.33) = -(-2.33) + 3 * Real.sin (-2.33 * Real.pi / 3) := by
    rw [hu]
  have h2 : u (-0.81) = -(-0.81) + 3 * Real.sin (-0.81 * Real.pi / 3) := by
    rw [hu]
  have h3 : u (0.81) = -(0.81) + 3 * Real.sin (0.81 * Real.pi / 3) := by
    rw [hu]
  have h4 : u (2.33) = -(2.33) + 3 * Real.sin (2.33 * Real.pi / 3) := by
    rw [hu]
  rw [h1, h2, h3, h4]
  have h5 : Real.sin (-2.33 * Real.pi / 3) = - Real.sin (2.33 * Real.pi / 3) := by
    have h1 : Real.sin (-2.33 * Real.pi / 3) = Real.sin (- (2.33 * Real.pi / 3)) := by ring_nf
    rw [h1]
    rw [show Real.sin (- (2.33 * Real.pi / 3)) = - Real.sin (2.33 * Real.pi / 3) by rw [Real.sin_neg]]
  have h6 : Real.sin (-0.81 * Real.pi / 3) = - Real.sin (0.81 * Real.pi / 3) := by
    have h2 : Real.sin (-0.81 * Real.pi / 3) = Real.sin (- (0.81 * Real.pi / 3)) := by ring_nf
    rw [h2]
    rw [show Real.sin (- (0.81 * Real.pi / 3)) = - Real.sin (0.81 * Real.pi / 3) by rw [Real.sin_neg]]
  rw [h5, h6]
  ring