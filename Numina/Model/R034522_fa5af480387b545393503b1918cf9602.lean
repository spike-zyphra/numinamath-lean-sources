import Mathlib

theorem algebra_214883 (a x : ℝ) (ha : a > 0) (hx : x > 0) :
    {y : ℝ | 
      let original_price := a
      let original_quantity := x
      let new_price := a * (1 + 30 / 100)
      let new_spending := a * x * (1 + 15 / 100)
      let new_quantity := new_spending / new_price
      y = (original_quantity - new_quantity) / original_quantity * 100
    } = {3 / 26 * 100} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Case where y is in the left side: prove y = 3 / 26 * 100
    intro hy
    have eq1 : y = (x - ((a * x * (1 + 15 / 100)) / (a * (1 + 30 / 100)))) / x * 100 := by
      linarith [hy]
    have eq4 : y = 3 / 26 * 100 := by
      have h12 : a > 0 := ha
      have h13 : x > 0 := hx
      have h14 : a ≠ 0 := by linarith
      have h15 : x ≠ 0 := by linarith
      rw [eq1]
      have eq17 : (x - ((a * x * (1 + 15 / 100)) / (a * (1 + 30 / 100)))) / x * 100 = 3 / 26 * 100 := by
        field_simp [h14, h15]
        ring_nf
      linarith [eq17]
    linarith [eq4]
  · -- Case where y = 3 / 26 * 100: prove y is in the left side
    intro hy
    rw [hy]
    have eq17 : (x - ((a * x * (1 + 15 / 100)) / (a * (1 + 30 / 100)))) / x * 100 = 3 / 26 * 100 := by
      have h12 : a > 0 := ha
      have h13 : x > 0 := hx
      have h14 : a ≠ 0 := by linarith
      have h15 : x ≠ 0 := by linarith
      field_simp [h14, h15]
      ring_nf
    linarith [eq17]