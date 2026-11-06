import Mathlib

theorem algebra_3759 {f : ℝ → ℝ} (hf : f = fun x => x^5 + x^3 + 1) (a : ℝ) (h : f (-a) = 5) : f a = -3 := by
  rw [hf] at h
  have h_eq : (-a)^5 + (-a)^3 + 1 = 5 := by 
    simpa using h
  have h1 : (-a)^5 = -a^5 := by
    ring_nf
  have h2 : (-a)^3 = -a^3 := by
    ring_nf
  rw [h1, h2] at h_eq
  have h3 : a^5 + a^3 = -4 := by
    linarith
  have ha : f a = a^5 + a^3 + 1 := by
    rw [hf]
  rw [ha]
  linarith [h3]