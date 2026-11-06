import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11903 {r : ℝ → ℝ} (hr : r = λ x => 1 / (1 - x) ^ 2) :
  r '' (univ \ {1}) = Set.Ioi 0 := by
  ext y
  simp [hr, Set.mem_image, Set.mem_setOf_eq, Set.mem_Ioi]
  constructor
  · -- Assume y in image of r on ℝ \ {1}
    rintro ⟨x, hx, rfl⟩
    have h1 : x ≠ 1 := by
      simpa using hx
    have h2 : (1 - x) ≠ 0 := by
      intro h
      apply h1
      linarith
    have h3 : (1 - x) ^ 2 > 0 := by
      apply pow_two_pos_of_ne_zero
      exact h2
    positivity
  · -- Assume y > 0, need to find x ≠ 1 such that r(x) = y
    intro hy
    have h1 : y > 0 := by simpa using hy
    use 1 - Real.sqrt (1 / y)
    constructor
    · -- Show that 1 - sqrt (1 / y) ≠ 1
      by_contra h
      have h2 : Real.sqrt (1 / y) = 0 := by linarith
      have h3 : Real.sqrt (1 / y) > 0 := by
        apply Real.sqrt_pos.mpr
        positivity
      linarith
    · -- Show that r(x) = y
      have h2 : 1 / (1 - (1 - Real.sqrt (1 / y)) ) ^ 2 = y := by
        have h3 : (1 - (1 - Real.sqrt (1 / y)) ) = Real.sqrt (1 / y) := by ring
        rw [h3]
        have h4 : (Real.sqrt (1 / y) ) ^ 2 = 1 / y := Real.sq_sqrt (by positivity)
        rw [h4]
        field_simp
        <;> linarith
      simpa using h2