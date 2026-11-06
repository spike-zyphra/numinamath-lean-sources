import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_225568 {f : ℝ → ℝ}
  (hf : ∀ x > 0, f x = ((x + 1 / x) ^ 6 - (x ^ 6 + 1 / x ^ 6) - 2) / ((x + 1 / x) ^ 3 + (x ^ 3 + 1 / x ^ 3))) :
  IsLeast {y | ∃ x > 0, f x = y} 6 := by
  have h1 : ∀ x > 0, f x = 3 * (x + 1 / x) := by
    intro x hx
    rw [hf x hx]
    have h2 : x ≠ 0 := by linarith
    have eq1 : (x + 1 / x) ^ 6 - (x ^ 6 + 1 / x ^ 6) - 2 = ((x + 1 / x) ^ 3 - (x ^ 3 + 1 / x ^ 3)) * ((x + 1 / x) ^ 3 + (x ^ 3 + 1 / x ^ 3)) := by
      field_simp
      ring
    have eq2 : (x + 1 / x) ^ 3 - (x ^ 3 + 1 / x ^ 3) = 3 * (x + 1 / x) := by
      field_simp at *
      ring
    have eq3 : (x + 1 / x) ^ 6 - (x ^ 6 + 1 / x ^ 6) - 2 = 3 * (x + 1 / x) * ((x + 1 / x) ^ 3 + (x ^ 3 + 1 / x ^ 3)) := by
      calc
        (x + 1 / x) ^ 6 - (x ^ 6 + 1 / x ^ 6) - 2 = ((x + 1 / x) ^ 3 - (x ^ 3 + 1 / x ^ 3)) * ((x + 1 / x) ^ 3 + (x ^ 3 + 1 / x ^ 3)) := by
          rw [eq1]
        _ = (3 * (x + 1 / x)) * ((x + 1 / x) ^ 3 + (x ^ 3 + 1 / x ^ 3)) := by
          rw [eq2]
          <;> ring
        _ = 3 * (x + 1 / x) * ((x + 1 / x) ^ 3 + (x ^ 3 + 1 / x ^ 3)) := by
          ring
    rw [eq3]
    field_simp
    <;> ring_nf <;> field_simp <;> ring
  constructor
  · -- Show 6 is in the set
    use 1
    constructor
    · norm_num
    · -- Show f 1 = 6
      rw [h1 1 (by norm_num)]
      norm_num
  · -- Show 6 is the least element
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    rw [h1 x hx] at hfx
    have h2 : x + 1 / x ≥ 2 := by
      have hx2 : x * (1 / x) = 1 := by
        field_simp
      have hx10 : x > 0 := hx
      have h5 : x + 1 / x - 2 ≥ 0 := by
        have h6 : x + 1 / x - 2 = (x - 1) ^ 2 / x := by
          field_simp
          <;> ring_nf <;> field_simp
        rw [h6]
        have h7 : (x - 1) ^ 2 ≥ 0 := sq_nonneg (x - 1)
        have h8 : (x - 1) ^ 2 / x ≥ 0 := by
          apply div_nonneg
          linarith
          linarith
        linarith
      linarith
    linarith