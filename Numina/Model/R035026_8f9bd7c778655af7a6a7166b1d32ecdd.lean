import Mathlib

open Real Int Nat Set
open scoped BigOperators

theorem inequalities_182583 (α β : ℝ) :
  ⌊2 * α⌋ + ⌊2 * β⌋ ≥ ⌊α⌋ + ⌊β⌋ + ⌊α + β⌋ := by
  let n := ⌊α⌋
  let m := ⌊β⌋
  have h1 : (n : ℝ) ≤ α := by exact Int.floor_le α
  have h2 : α < (n + 1 : ℝ) := by exact Int.lt_floor_add_one α
  have h3 : (m : ℝ) ≤ β := by exact Int.floor_le β
  have h4 : β < (m + 1 : ℝ) := by exact Int.lt_floor_add_one β
  have h5 : (n + m : ℝ) ≤ α + β := by linarith
  have h6 : α + β < (n + m + 2 : ℝ) := by linarith
  have h7 : ⌊α + β⌋ = n + m ∨ ⌊α + β⌋ = n + m + 1 := by
    have h8 : (⌊α + β⌋ : ℝ) ≤ α + β := by exact Int.floor_le (α + β)
    have h9 : α + β < (⌊α + β⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one (α + β)
    have h10 : ⌊α + β⌋ ≤ n + m + 1 := by
      by_contra h
      push_neg at h
      have : ⌊α + β⌋ ≥ n + m + 2 := by omega
      have h12 : (⌊α + β⌋ : ℝ) ≥ (n + m + 2 : ℝ) := by exact_mod_cast this
      nlinarith
    have h11 : ⌊α + β⌋ ≥ n + m := by
      by_contra h
      push_neg at h
      have : ⌊α + β⌋ ≤ n + m - 1 := by omega
      have h12 : (⌊α + β⌋ : ℝ) ≤ (n + m - 1 : ℝ) := by exact_mod_cast this
      nlinarith
    omega
  rcases h7 with (h7 | h7)
  · -- case `⌊α + β⌋ = n + m`
    have h8 : ⌊α + β⌋ = n + m := h7
    have h9 : ⌊2 * α⌋ ≥ 2 * n := by 
      have h10 : (n : ℝ) ≤ α := by exact Int.floor_le α
      have h11 : (2 * (n : ℝ) : ℝ) ≤ 2 * α := by linarith
      have h12 : (2 * n : ℝ) ≤ 2 * α := by
        norm_num at h11 ⊢
        linarith
      have h13 : ⌊2 * α⌋ ≥ ⌊(2 * (n : ℝ) : ℝ)⌋ := by 
        apply Int.floor_le_floor
        nlinarith
      have h14 : ⌊(2 * (n : ℝ) : ℝ)⌋ = 2 * n := by
        simp [Int.floor_eq_iff, mul_add, mul_comm]
      linarith
    have h10 : ⌊2 * β⌋ ≥ 2 * m := by
      have h11 : (m : ℝ) ≤ β := by exact Int.floor_le β
      have h12 : (2 * (m : ℝ) : ℝ) ≤ 2 * β := by linarith
      have h13 : ⌊2 * β⌋ ≥ ⌊(2 * (m : ℝ) : ℝ)⌋ := by
        apply Int.floor_le_floor
        nlinarith
      have h14 : ⌊(2 * (m : ℝ) : ℝ)⌋ = 2 * m := by
        simp [Int.floor_eq_iff, mul_add, mul_comm]
      linarith
    omega
  · -- case `⌊α + β⌋ = n + m + 1`
    have h8 : ⌊α + β⌋ = n + m + 1 := h7
    have h17 : α + β ≥ (n + m + 1 : ℝ) := by
      have h82 : (⌊α + β⌋ : ℝ) ≤ α + β := by exact Int.floor_le (α + β)
      have h83 : (⌊α + β⌋ : ℝ) = (n + m + 1 : ℝ) := by exact_mod_cast h8
      linarith
    have h16 : ⌊2 * α⌋ + ⌊2 * β⌋ ≥ 2 * n + 2 * m + 1 := by
      by_cases h195 : α < (n + 0.5 : ℝ)
      · -- case `α < n + 0.5`
        have h164 : ⌊2 * α⌋ = 2 * n := by
          have h166 : (n : ℝ) ≤ α := by exact Int.floor_le α
          have h167 : α < (n + 0.5 : ℝ) := h195
          have h170 : (2 * n : ℝ) ≤ 2 * α := by nlinarith
          have h171 : 2 * α < (2 * n + 1 : ℝ) := by
            nlinarith
          rw [Int.floor_eq_iff]
          constructor <;> (try norm_num) <;> nlinarith
        have h176 : ⌊2 * β⌋ ≥ 2 * m + 1 := by
          have h184 : β ≥ (m + 0.5 : ℝ) := by
            nlinarith [show α + β ≥ (n + m + 1 : ℝ) from h17]
          have h187 : 2 * β ≥ (2 * m + 1 : ℝ) := by
            nlinarith
          have h189 : ⌊2 * β⌋ ≥ ⌊(2 * m + 1 : ℝ)⌋ := by
            apply Int.floor_le_floor
            nlinarith
          have h192 : ⌊(2 * m + 1 : ℝ)⌋ = 2 * m + 1 := by
            simp [Int.floor_eq_iff, mul_add, mul_comm]
          linarith
        omega
      · -- case `α ≥ n + 0.5`
        have h197 : α ≥ (n + 0.5 : ℝ) := by nlinarith
        have h164 : ⌊2 * α⌋ ≥ 2 * n + 1 := by
          have h187 : 2 * α ≥ (2 * n + 1 : ℝ) := by
            nlinarith
          have h189 : ⌊2 * α⌋ ≥ ⌊(2 * n + 1 : ℝ)⌋ := by
            apply Int.floor_le_floor
            nlinarith
          have h192 : ⌊(2 * n + 1 : ℝ)⌋ = 2 * n + 1 := by
            simp [Int.floor_eq_iff, mul_add, mul_comm]
          linarith
        have h176 : ⌊2 * β⌋ ≥ 2 * m := by
          have h11 : (m : ℝ) ≤ β := by exact Int.floor_le β
          have h12 : (2 * (m : ℝ) : ℝ) ≤ 2 * β := by linarith
          have h13 : ⌊2 * β⌋ ≥ ⌊(2 * (m : ℝ) : ℝ)⌋ := by
            apply Int.floor_le_floor
            nlinarith
          have h14 : ⌊(2 * (m : ℝ) : ℝ)⌋ = 2 * m := by
            simp [Int.floor_eq_iff, mul_add, mul_comm]
          linarith
        omega
    omega