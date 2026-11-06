import Mathlib

theorem algebra_143303 {f : ℕ → ℝ}
    (h₁ : f 1 = 3 / 2)
    (h₂ : ∀ x y, f (x + y) = (1 + y / (x + 1)) * f x + (1 + x / (y + 1)) * f y +
      x ^ 2 * y + x * y + x * y ^ 2) :
    ∀ x, f x = (1 / 4) * x * (x + 1) * (2 * x + 1) := by

  have h3 : f 0 = 0 := by
    specialize h₂ 0 0
    norm_num at h₂ ⊢
    linarith

  intro x
  induction x with
  | zero =>
    rw [h3]
    all_goals norm_num
  | succ x ihx =>
    have h5 : f (x + 1) = (1 + (1 : ℝ) / ((x + 1 : ℝ))) * f x + (1 + (x : ℝ) / (2 : ℝ)) * f 1 + (x : ℝ) ^ 2 + (x : ℝ) + (x : ℝ) := by
      specialize h₂ x 1
      norm_num at h₂ ⊢
      <;> linarith [h₁]
    
    rw [h5]
    rw [h₁]
    rw [ihx]
    field_simp at *
    ring_nf