import Mathlib

/-Solve the inequality system: $\left\{{\begin{array}{l}{4x-8≤0}\\{\frac{{x+3}}{2}＞3-x}\end{array}}\right.$.-/
theorem algebra_9182 :
  ∀ (x : ℝ), (4 * x - 8 ≤ 0 ∧ (x + 3) / 2 > 3 - x) ↔ (x > 1 ∧ x ≤ 2) := by
  intro x
  have second_ineq_equiv : (x + 3) / 2 > 3 - x ↔ x > 1 := by
    constructor
    · intro h
      -- Multiply both sides by 2 (positive)
      have pos_two : 0 < (2 : ℝ) := by norm_num
      have h1 : 2 * ((x + 3) / 2) > 2 * (3 - x) := by
        exact mul_lt_mul_of_pos_left h pos_two
      -- Simplify left side
      have h2 : 2 * ((x + 3) / 2) = x + 3 := by
        field_simp
      -- Simplify right side
      have h3 : 2 * (3 - x) = 6 - 2*x := by
        ring
      rw [h2, h3] at h1
      linarith
    · intro h
      -- Start with x > 1 and convert it to our target inequality
      have h1 : (x + 3)/2 > 3 - x := by
        linarith
      have pos_two : 0 < (2 : ℝ) := by norm_num
      calc (x + 3) / 2 = (2 * ((x + 3) / 2)) / 2 := by ring_nf
      _ > (2 * (3 - x)) / 2 := by 
        have left_eq : 2 * ((x + 3) / 2) / 2 = (x + 3) / 2 := by ring
        have right_eq : 2 * (3 - x) / 2 = 3 - x := by ring
        rw [left_eq, right_eq]
        exact h1
      _ = 3 - x := by
        field_simp
  have first_ineq_equiv: 4 * x - 8 ≤ 0 ↔ x ≤ 2 := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  constructor
  · intro h
    constructor
    · exact (second_ineq_equiv.mp h.2)
    · exact (first_ineq_equiv.mp h.1)
  · intro h
    constructor
    · exact (first_ineq_equiv.mpr h.2)
    · exact (second_ineq_equiv.mpr h.1)