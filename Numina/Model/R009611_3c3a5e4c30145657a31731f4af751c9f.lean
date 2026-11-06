import Mathlib

theorem algebra_21907 {p q r x : ℝ} :
    {x | (x - p) * (x - q) = (r - p) * (r - q)} = {r, p + q - r} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Forward direction: if $(x-p)(x-q) = (r-p)(r-q)$, then $x = r$ or $x = p+q-r$
    intro h
    have h1 : (x - p) * (x - q) - (r - p) * (r - q) = 0 := by linarith 
    have h2 : (x - r) * (x - (p + q - r)) = 0 := by
      ring_nf at h1 ⊢
      linarith 
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case where $x - r = 0$
      left
      linarith 
    · -- Case where $x - (p + q - r) = 0$
      right
      linarith 
  · -- Backward direction: if $x = r$ or $x = p + q - r$, then $(x-p)(x-q) = (r-p)(r-q)$
    rintro (h | h)
    · -- Case where $x = r$
      rw [h]
    · -- Case where $x = p + q - r$
      rw [h]
      ring