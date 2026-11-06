import Mathlib

theorem algebra_10305 {h : ℝ → ℝ} (h_def : ∀ x, h (4 * x - 1) = 2 * x + 7) : {x | h x = x} = {15} := by
  have h_eq : ∀ y, h y = (y + 15) / 2 := by
    intro y
    let x := (y + 1) / 4
    have hx : 4 * x - 1 = y := by
      ring_nf
    rw [←hx, h_def]
    field_simp
    <;> ring
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume h x = x, prove x = 15
    intro hx
    rw [h_eq x] at hx
    linarith
  · -- Assume x = 15, prove h x = x
    intro hx
    rw [hx]
    rw [h_eq 15]
    norm_num