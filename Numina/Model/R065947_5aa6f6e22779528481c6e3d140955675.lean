import Mathlib

theorem algebra_109675 {f : ℝ → ℝ} (hf : ∀ x, f x = a * x ^ 2 - Real.sqrt 2)
    (ha : 0 < a) (h : f (f (Real.sqrt 2)) = -Real.sqrt 2) :
    a = Real.sqrt 2 / 2 := by

  have h1 : f (Real.sqrt 2) = 2 * a - Real.sqrt 2 := by
    rw [hf]
    have h2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    simp [h2]
    <;> ring_nf <;> norm_num

  rw [h1] at h

  have h3 : f (2 * a - Real.sqrt 2) = a * (2 * a - Real.sqrt 2) ^ 2 - Real.sqrt 2 := by
    apply hf
  rw [h3] at h

  have h4 : a * (2 * a - Real.sqrt 2) ^ 2 = 0 := by
    linarith

  have h5 : (2 * a - Real.sqrt 2) ^ 2 = 0 := by
    nlinarith
  have h6 : 2 * a - Real.sqrt 2 = 0 := by
    rw [sq_eq_zero_iff] at h5
    exact h5

  linarith