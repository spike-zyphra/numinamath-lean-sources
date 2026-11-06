import Mathlib

theorem algebra_198477 {f : ℝ → ℝ} (hf : f = fun x => 1 / (1 - x)) :
    ∀ x, x ≠ 0 ∧ x ≠ 1 → f (f (f x)) = x := by 
  intro x h
  have hx1 : x ≠ 0 := h.1
  have hx2 : x ≠ 1 := h.2
  simp [hf]
  have hx3 : 1 - x ≠ 0 := by 
    intro h'
    apply hx2
    linarith
  have hx4 : x ≠ 0 := hx1
  field_simp [(show (1 - x) ≠ 0 by
    exact hx3
  ), (show x ≠ 0 by
    exact hx1
  ), (show x - 1 ≠ 0 by
    intro h'
    apply hx2 
    linarith
  )]
  <;> ring_nf <;> norm_num <;> tauto