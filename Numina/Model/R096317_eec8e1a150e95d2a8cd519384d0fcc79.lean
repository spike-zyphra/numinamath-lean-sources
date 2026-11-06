import Mathlib

theorem algebra_195083 {A : ℝ → ℝ} (hA : ∀ x, x ≠ 2 → A x = abs ((abs (x - 2) + 4) / (x - 2)) * (x ^ 2 - 4)) :
    ∀ x, x > 2 → A x = (x + 2) ^ 2 := by
  intro x hx
  have h1 : x ≠ 2 := by linarith
  specialize hA x h1
  rw [hA]
  have h2 : abs (x - 2) = x - 2 := by
    rw [abs_of_pos]
    linarith
  have h3 : (abs (x - 2) + 4) = x + 2 := by
    rw [h2]
    ring
  have h4 : (abs (x - 2) + 4) / (x - 2) = (x + 2) / (x - 2) := by
    rw [h3]
  have h5 : abs ((x + 2) / (x - 2)) = (x + 2) / (x - 2) := by
    have h6 : (x + 2) / (x - 2) ≥ 0 := by
      apply div_nonneg
      linarith
      linarith
    rw [abs_of_nonneg h6]
  have h7 : abs ((abs (x - 2) + 4) / (x - 2)) = (x + 2) / (x - 2) := by
    rw [h4]
    rw [h5]
  rw [h7]
  have h8 : (x ^ 2 - 4) = (x - 2) * (x + 2) := by
    ring
  rw [h8]
  field_simp [(show x - 2 ≠ 0 by
    intro h
    apply h1
    linarith
  )]
  <;> ring_nf <;> norm_num
  <;> linarith