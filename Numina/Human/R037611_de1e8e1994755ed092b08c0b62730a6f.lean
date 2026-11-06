import Mathlib

theorem algebra_168211 {x : ℕ} {t : ℝ} (hx : x > 75)
   (h1 : t / (x - 75) - t / x = 20) (h2 : t / x - t / (x + 100) = 15) :
    x = 300 := by
  have : (x - 75 : ℝ) > 0 := by simp; linarith
  field_simp [this] at *
  ring_nf at *
  have : (↑x * 1500 + ↑x ^ 2 * 15) / 100 = (-((x : ℝ) * 1500) + ↑x ^ 2 * 20) / 75 := by
    rw [h1.symm, h2.symm]
    simp
  field_simp at this
  ring_nf at this
  have : ((x : ℝ) - 0) = 0 ∨ ((x : ℝ) - 300) = 0 := by
     rw [←mul_eq_zero]
     linarith
  rcases this with (h | h)
  · simp at h
    omega
  · rw [sub_eq_zero] at h
    norm_cast at h
