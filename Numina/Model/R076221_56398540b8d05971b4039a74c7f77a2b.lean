import Mathlib

open Real
open scoped BigOperators

theorem algebra_197365 {c : ℚ} (M : Set (ℚ × ℚ)) (hM : M = {(x, y) | x + y = c}) :
    IsGreatest {z | ∃ a b : ℚ, (a, b) ∈ M ∧ z = a * b} (c ^ 2 / 4) := by
  constructor
  · -- Show that \( \frac{c^2}{4} \) belongs to the set
    use c / 2, c / 2
    constructor
    · -- Check that (c/2, c/2) ∈ M
      rw [hM]
      simp
      <;> ring_nf <;> norm_num
      <;> tauto
    · -- Check that the product equals c^2/4
      ring_nf
  · -- Show that \( \frac{c^2}{4} \) is the greatest
    intro z hz
    rcases hz with ⟨a, b, hMab, hz⟩
    rw [hM] at hMab
    simp at hMab
    have h4 : b = c - a := by linarith
    rw [hz]
    rw [h4]
    have h5 : a * (c - a) ≤ (c ^ 2 / 4 : ℚ) := by
      have h : (a - c / 2 : ℚ) ^ 2 ≥ 0 := by
        apply sq_nonneg
      linarith
    linarith