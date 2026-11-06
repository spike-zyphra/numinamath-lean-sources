import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10178 : {p : ℝ | ∀ q > 0, p + q ≠ 0 ∧ 3 * (p * q^2 + p^2 * q + 3 * q^2 + 3 * p * q) / (p + q) > 2 * p^2 * q} = Ico 0 3 := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · -- First implication: if p satisfies the condition, then p ∈ [0, 3)
    intro h
    have hp1 : p ≥ 0 := by
      by_contra hp
      push_neg at hp
      have h2 := h (-p) (by linarith)
      have h21 : p + (-p) = (0 : ℝ) := by linarith
      have h22 := h2.1
      contradiction
    have hp2 : p < 3 := by
      have h2 := h 1 (by norm_num)
      have h21 : p + (1 : ℝ) ≠ 0 := h2.1
      have h22 : (3 * (p * (1 : ℝ)^2 + p^2 * (1 : ℝ) + 3 * (1 : ℝ)^2 + 3 * p * (1 : ℝ)) / (p + (1 : ℝ)) > 2 * p^2 * (1 : ℝ)) := h2.2
      have hp11 : p ≥ 0 := hp1
      have hp14 : p + 1 > 0 := by
        nlinarith [hp11]
      have h25 : (3 * (p * (1 : ℝ)^2 + p^2 * (1 : ℝ) + 3 * (1 : ℝ)^2 + 3 * p * (1 : ℝ)) / (p + 1) ) = 3 * (p + 3) := by
        have h24 : 3 * (p * (1 : ℝ)^2 + p^2 * (1 : ℝ) + 3 * (1 : ℝ)^2 + 3 * p * (1 : ℝ)) = 3 * (p^2 + 4 * p + 3) := by nlinarith
        rw [h24]
        have hp15 : 3 * (p^2 + 4 * p + 3) = 3 * (p + 1) * (p + 3) := by nlinarith
        rw [hp15]
        field_simp [hp14]
        all_goals nlinarith
      nlinarith [h25, h22, sq_nonneg (p - 3)]
    constructor
    · -- Show that 0 ≤ p
      linarith
    · -- Show that p < 3
      linarith
  · -- Second implication: if p ∈ [0, 3), then it satisfies the condition
    rintro ⟨hp0, hp3⟩
    intro q hq
    have hpq : p + q ≠ 0 := by
      have hp0' : p ≥ 0 := hp0
      have hq' : q > 0 := hq
      have hpq' : p + q > 0 := by nlinarith
      linarith
    have h41 : 3 * (p * q^2 + p^2 * q + 3 * q^2 + 3 * p * q) / (p + q) = 3 * q * (p + 3) := by
      have hpq1 : p + q ≠ 0 := hpq
      have h42 : 3 * (p * q^2 + p^2 * q + 3 * q^2 + 3 * p * q) = 3 * q * (p + 3) * (p + q) := by
        ring_nf
      rw [h42]
      field_simp [hpq1]
      <;> nlinarith
    constructor
    · exact hpq
    · -- Show the inequality
      have h5 : 3 * (p * q^2 + p^2 * q + 3 * q^2 + 3 * p * q) / (p + q) = 3 * q * (p + 3) := h41
      have h6 : 3 * q * (p + 3) > 2 * p^2 * q := by
        have h7 : q > 0 := hq
        have hp8 : p < 3 := by linarith
        have hp9 : 3 * (p + 3) > 2 * p^2 := by
          nlinarith [sq_nonneg (p - 3)]
        nlinarith [hp9]
      linarith [h5, h6]