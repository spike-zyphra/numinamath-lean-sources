import Mathlib

theorem algebra_145066 {f : ℕ → ℝ} (h1 : f 1 = 3 / 2)
    (hf : ∀ x y, f (x + y) = (1 + y / (x + 1 : ℝ)) * f x + (1 + x / (y + 1 : ℝ)) * f y +
      x ^ 2 * y + x * y + x * y ^ 2) :
    ∀ x, f x = (1 / 4) * x * (x + 1) * (2 * x + 1) := by

  have h0 : f 0 = 0 := by
    have eq1 := hf 0 0
    norm_num at eq1
    linarith

  intro x
  induction x with
  | zero =>
    rw [h0]
    norm_num
  | succ x ih =>
    have eq1 := hf x 1
    have eq2 : f (x + 1) = (1 + (1 : ℝ) / (x + 1 : ℝ)) * f x + (1 + (x : ℝ) / (2 : ℝ)) * f 1 + (x ^ 2 * (1 : ℝ) + (x : ℝ) * (1 : ℝ) + (x : ℝ) * (1 : ℝ) ^ 2) := by
      simp [eq1]
      <;> ring_nf <;> field_simp <;> ring
    rw [eq2]
    rw [ih]
    rw [h1]
    field_simp
    ring_nf