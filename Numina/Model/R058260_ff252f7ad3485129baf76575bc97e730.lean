import Mathlib

theorem algebra_12785 {a : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 2 - Real.sqrt 2)
    (h : f (f (Real.sqrt 2)) = -Real.sqrt 2) :
    a = 0 ∨ a = Real.sqrt 2 / 2 := by

  have h1 : f (Real.sqrt 2) = 2 * a - Real.sqrt 2 := by
    rw [hf]
    have h2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
    simp [h2]
    <;> ring

  have h2 : f (f (Real.sqrt 2)) = a * (2 * a - Real.sqrt 2) ^ 2 - Real.sqrt 2 := by
    rw [h1] at *
    apply hf

  rw [h2] at h

  have eq1 : a * (2 * a - Real.sqrt 2) ^ 2 = 0 := by
    nlinarith [h]

  cases (mul_eq_zero.mp eq1) with
  | inl h3 =>
    left
    exact h3
  | inr h4 =>
    have h5 : 2 * a - Real.sqrt 2 = 0 := by
      rw [sq_eq_zero_iff] at h4
      linarith
    have ha : a = Real.sqrt 2 / 2 := by
      linarith
    right
    exact ha