import Mathlib

theorem algebra_97603 (V : ℝ → ℝ) (hV : ∀ x, V x = V 0 + 4 * (x / 3)) (hV' : V 32 = 24) :
    V 20 = 8 := by
  have h0 : V 32 = V 0 + 4 * (32 / 3) := hV 32
  rw [hV'] at h0
  have hV0 : V 0 = -56 / 3 := by
    linarith
  have h20 : V 20 = V 0 + 4 * (20 / 3) := hV 20
  rw [hV0] at h20
  norm_num at h20 ⊢
  linarith