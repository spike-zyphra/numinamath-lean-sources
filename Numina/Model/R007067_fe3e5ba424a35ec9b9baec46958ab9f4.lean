import Mathlib

theorem algebra_608379 (H M F : ℚ) (h1 : 3 * H + 5 * M + F = 23.5)
(h2 : 5 * H + 9 * M + F = 39.5) : 2 * H + 2 * M + 2 * F = 15 := by
  have eq1 : 2 * H + 4 * M = 16 := by
    have h3 : 5 * H + 9 * M + F - (3 * H + 5 * M + F) = 39.5 - 23.5 := by linarith
    ring_nf at h3 ⊢
    linarith
  have eq2 : H + 2 * M = 8 := by
    linarith
  have hH : H = 8 - 2 * M := by
    linarith [eq2]
  have hF : F = M - 0.5 := by
    rw [hH] at h1
    ring_nf at h1 ⊢
    linarith
  rw [hH, hF]
  ring_nf
  <;> linarith