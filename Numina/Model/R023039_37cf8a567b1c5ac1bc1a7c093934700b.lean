import Mathlib

theorem algebra_6157 (s : Set ℝ) (hs : s = {a : ℝ | 0 < a ∧ a ≠ 3 ∧ a / 8 + 1 / (3 - a) = 5 * a / 8}) :
  s.Finite ∧ ((fin : s.Finite) → fin.toFinset.sum id = 3) := by
  have h1 : s = {1, 2} := by
    ext a
    simp only [hs, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume h: 0 < a ∧ a ≠ 3 ∧ a / 8 + 1 / (3 - a) = 5 * a / 8, prove a ∈ {1, 2}
      rintro ⟨ha_pos, ha_ne3, heq⟩
      have eq1 : a / 8 + 1 / (3 - a) = 5 * a / 8 := heq
      have h2 : 3 - a ≠ 0 := by
        intro h'
        apply ha_ne3
        linarith
      have eq2 : a * (3 - a) + 8 = 5 * a * (3 - a) := by
        have eq3 : a / 8 + 1 / (3 - a) = 5 * a / 8 := heq
        have eq4 : (a / 8 + 1 / (3 - a)) * (8 * (3 - a)) = (5 * a / 8) * (8 * (3 - a)) := by
          rw [eq3]
        have eq5 : (a / 8 + 1 / (3 - a)) * (8 * (3 - a)) = a * (3 - a) + 8 := by
          have h1 : 3 - a ≠ 0 := h2
          field_simp [h1]
          <;> ring
        have eq6 : (5 * a / 8) * (8 * (3 - a)) = 5 * a * (3 - a) := by
          field_simp [show 3 - a ≠ 0 by assumption]
          <;> ring
        rw [eq5, eq6] at eq4
        linarith
      have eq3 : a ^ 2 - 3 * a + 2 = 0 := by
        nlinarith
      have eq4 : (a - 1) * (a - 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp eq4) with ha1 ha2
      · -- Case a = 1
        left
        linarith
      · -- Case a = 2
        right
        linarith
    · -- Assume a ∈ {1, 2}, prove h
      rintro (rfl | rfl)
      · -- a = 1
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show equation
          norm_num
      · -- a = 2
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show equation
          norm_num
  rw [h1]
  constructor
  · -- Show {1, 2} is finite
    simp
  · -- Show sum = 3
    intro fin
    simp [h1]
    <;> norm_num