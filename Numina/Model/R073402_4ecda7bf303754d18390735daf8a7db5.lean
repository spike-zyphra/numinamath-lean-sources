import Mathlib

theorem number_theory_5482 (f : ℤ → ℤ) (h : ∀ m n, f m * f n = f (m * n)) (hf : f 1 = 1) : f (-1) = 1 ∨ f (-1) = -1 := by
  have h1 : f (-1) * f (-1) = f ((-1 : ℤ) * (-1 : ℤ)) := h (-1) (-1)
  have h2 : (-1 : ℤ) * (-1 : ℤ) = 1 := by norm_num
  rw [h2] at h1
  rw [hf] at h1
  have h3 : f (-1) ^ 2 = 1 := by
    nlinarith
  have h4 : f (-1) = 1 ∨ f (-1) = -1 := by
    rw [sq_eq_one_iff] at h3
    exact h3
  exact h4