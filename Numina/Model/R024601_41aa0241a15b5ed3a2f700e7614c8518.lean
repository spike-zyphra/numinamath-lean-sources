import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_297162 {a : ℝ} (ha : a ≠ 0) :
    (∀ x ∈ Icc 1 2, 4 * x / a + 1 / x ≥ 4) ↔ a ∈ Ioc 0 (4 / 3) := by
  constructor
  · -- First direction: if the inequality holds for all x in [1,2], then a ∈ (0, 4/3].
    intro h
    have h1 := h 1 (by norm_num)
    have h2 : 4 / a + 1 ≥ 4 := by
      have h' : 4 * 1 / a + 1 / (1 : ℝ) ≥ 4 := by simpa using h1
      norm_num at h' ⊢
      linarith
    have h3 : 4 / a ≥ 3 := by linarith
    have ha1 : 0 < a := by
      by_contra h'
      push_neg at h'
      have ha2 : a < 0 := by
        by_contra h'
        push_neg at h'
        have ha3 : a = 0 := by linarith
        contradiction
      have h4 : 4 / a < 0 := by
        apply div_neg_of_pos_of_neg
        norm_num
        linarith
      linarith
    have ha2 : a ≤ 4 / 3 := by
      have h4 : 4 / a ≥ 3 := h3
      have ha1 : 0 < a := ha1
      have h6 : 4 ≥ 3 * a := by
        have h7 : 4 / a ≥ 3 := h4
        apply (le_div_iff₀ (by linarith)).mp at h7
        linarith
      linarith
    constructor
    · linarith
    · linarith
  · -- Second direction: if a ∈ (0, 4/3], then the inequality holds for all x in [1,2].
    rintro ⟨ha1, ha2⟩
    intro x hx
    rcases hx with ⟨hx1, hx2
      ⟩
    have hx3 : 0 < x := by linarith
    have ha4 : 0 < a := by linarith
    have h7 : 4 * x / a + 1 / x - 4 ≥ 0 := by
      have h11 : 4 * x / a + 1 / x - 4 = (4 * x ^ 2 + a - 4 * a * x) / (a * x) := by
        field_simp
        <;> ring
      rw [h11] at *
      apply div_nonneg
      nlinarith [sq_nonneg (x - 1), sq_nonneg (a - 4 / 3), sq_nonneg (x - 4 / 3), sq_nonneg (x - a / 2), mul_nonneg (show 0 ≤ x - 1 by nlinarith) (show 0 ≤ x - 1 by nlinarith)]
      all_goals
      positivity
    linarith