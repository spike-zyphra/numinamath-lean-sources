import Mathlib

theorem P4192 {f : ℝ → ℝ} (h0 : f 0 = 1 / 2)
    (ha : ∃ a, ∀ x y, f (x + y) = f x * f (a - y) + f y * f (a - x)) :
    ∃ c, ∀ x, f x = c := by
  rcases ha with ⟨a, ha⟩
  have ha00 := ha 0 0
  simp [h0] at ha00
  rw [← mul_add, ← two_mul, ← mul_assoc, eq_comm] at ha00
  rw [show 2⁻¹ * 2 = (1 : ℝ) by ring, one_mul] at ha00
  have hax x := ha x 0
  simp [h0, ha00] at hax
  replace hax x : f x = f (a - x) := by
    linear_combination 2  * (hax x)
  have haxy x := ha x (a - x)
  simp [h0, ha00] at haxy
  replace haxy x : f x ^ 2 = 1 / 4 := by
    specialize haxy x
    rw [← hax x] at haxy
    linear_combination -1/2 * haxy
  use 1 / 2
  intro x
  specialize haxy x
  rw [show (1 : ℝ)/4=(1/2)^2 by norm_num, sq_eq_sq_iff_eq_or_eq_neg] at haxy
  rcases haxy with _ | haxy
  . assumption
  exfalso
  specialize hax (x / 2)
  specialize ha (x / 2) (x / 2)
  rw [← hax, ← pow_two] at ha
  have : 0 ≤ f x := by
    rw [show x = x / 2 + x / 2 by ring, ha]
    apply add_nonneg <;> apply sq_nonneg
  linarith
