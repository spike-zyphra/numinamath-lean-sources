import Mathlib

open Real

theorem algebra_6494 {x : ℝ} (hx : x = 2 / (1 - 3 / (2 + 2 / (1 - x)))) :
    x ≤ 4 := by
  by_contra h 
  push_neg at h 
  -- Assume x > 4, we'll get a contradiction
  have eq1 : x = 2 / (1 - 3 / (2 + 2 / (1 - x))) := hx
  have h2 : x - 4 > 0 := by linarith 
  -- We need to clear denominators to turn into polynomial equations.
  have h4 : 1 - x ≠ 0 := by
    nlinarith 
  -- Now manipulating expressions.
  have h6 : 2 + 2 / (1 - x) = (4 - 2 * x) / (1 - x) := by
    have h7 : 1 - x ≠ 0 := h4
    field_simp [h7]
    <;> ring 
  -- Now manipulate $1 - 3/(2 + 2/(1 - x))$.
  have h7 : 2 + 2 / (1 - x) ≠ 0 := by
    rw [h6]
    by_contra h 
    have h8 : (4 - 2 * x) / (1 - x) = 0 := by
      linarith 
    have h9 : 4 - 2 * x = 0 := by 
      have h10 : 1 - x ≠ 0 := h4 
      field_simp [h10] at h8 ⊢ 
      <;> linarith 
    have h11 : x = 2 := by
      linarith 
    nlinarith 
  -- Compute expression  $1 - 3/(2+2/(1-x))$.
  have h8 : 1 - 3 / (2 + 2 / (1 - x)) = (1 + x) / (4 - 2 * x) := by
    rw [h6]
    have h9 : 1 - 3 / ((4 - 2 * x) / (1 - x)) = (1 + x) / (4 - 2 * x) := by
      have h7' : (4 - 2 * x) / (1 - x) ≠ 0 := by
        by_contra h
        have h8 : (4 - 2 * x) / (1 - x) = 0 := by
          linarith 
        have h10 : 4 - 2 * x = 0 := by 
          have h10 : 1 - x ≠ 0 := h4 
          field_simp [h10] at h8 ⊢ 
          <;> linarith 
        have h11 : x = 2 := by
          linarith 
        nlinarith 
      have h11 : 4 - 2 * x ≠ 0 := by
        by_contra h 
        have h12 : x = 2 := by 
          linarith 
        nlinarith 
      field_simp [h7', h11] 
      <;> ring_nf 
      <;> field_simp [h7', h11] 
      <;> ring 
    exact h9
  -- Substituting now.
  rw [h8] at eq1 
  -- Now clear denominators
  have h10 : 1 + x ≠ 0 := by
    nlinarith 
  -- Manipulate to not have denominators
  field_simp [h10] at eq1 ⊢
  -- Now polynomial.
  nlinarith [sq_nonneg (x * (x + 5)), sq_nonneg ((x + 5 / 2) ), sq_nonneg (x - 2)]