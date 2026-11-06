import Mathlib

theorem algebra_326275 {x : ℝ} (hx : x ≠ 2 ∧ x ≠ 3 ∧ x ≠ 6 ∧ x ≠ 5) :
    ((x - 2) / 3 + (x - 3) / 2 = 3 / (x - 2) + 2 / (x - 3)) ∧
    ((x - 6) / 5 + (x - 5) / 6 = 5 / (x - 6) + 6 / (x - 5)) ↔ x = 0 := by
  constructor
  · -- Forward implication: if x is in both, then x = 0
    intro h
    rcases hx with ⟨hx1, hx2, hx3, hx4⟩
    rcases h with ⟨h1, h2⟩
    have eq1 : (x - 2) / 3 + (x - 3) / 2 = 3 / (x - 2) + 2 / (x - 3) := h1
    have eq2 : (x - 6) / 5 + (x - 5) / 6 = 5 / (x - 6) + 6 / (x - 5) := h2
    have eq3 : (x - 2) * (x - 3) * ((x - 2) / 3 + (x - 3) / 2) =
        (x - 2) * (x - 3) * (3 / (x - 2) + 2 / (x - 3)) := by
      rw [eq1]
    have eq4 : (x - 2) * (x - 3) * ((x - 2) / 3 + (x - 3) / 2) =
        ((x - 2) * (x - 3) * (2 * (x - 2) + 3 * (x - 3)) ) / (6 : ℝ) := by
      field_simp
      ring_nf
    have eq5 : (x - 2) * (x - 3) * (3 / (x - 2) + 2 / (x - 3)) =
        5 * x - 13 := by
      field_simp [(show x - 2 ≠ 0 by intro h'; apply hx1; linarith),
                  (show x - 3 ≠ 0 by intro h'; apply hx2; linarith)]
      ring_nf
    rw [eq4, eq5] at eq3
    have eq6 : (x - 2) * (x - 3) * (2 * (x - 2) + 3 * (x - 3)) = (6 : ℝ) * (5 * x - 13) := by
      have eq7 : ((x - 2) * (x - 3) * (2 * (x - 2) + 3 * (x - 3)) ) / (6 : ℝ) = (5 * x - 13) := by
        nlinarith [eq3]
      have eq8 : (x - 2) * (x - 3) * (2 * (x - 2) + 3 * (x - 3)) = (6 : ℝ) * (5 * x - 13) := by
        field_simp at eq7 ⊢
        <;> nlinarith [eq7, sq_pos_of_ne_zero (show x - 2 ≠ 0 by intro h'; apply hx1; linarith), sq_pos_of_ne_zero (show x - 3 ≠ 0 by intro h'; apply hx2; linarith)]
      linarith
    have eq7' : (x - 6) * (x - 5) * ((x - 6) / 5 + (x - 5) / 6) =
        (x - 6) * (x - 5) * (5 / (x - 6) + 6 / (x - 5)) := by
      rw [eq2]
    have eq8' : (x - 6) * (x - 5) * ((x - 6) / 5 + (x - 5) / 6) =
        ((x - 6) * (x - 5) * (6 * (x - 6) + 5 * (x - 5)) ) / (30 : ℝ) := by
      field_simp
      ring_nf
    have eq9' : (x - 6) * (x - 5) * (5 / (x - 6) + 6 / (x - 5)) =
        11 * x - 61 := by
      field_simp [(show x - 6 ≠ 0 by intro h'; apply hx3; linarith),
                  (show x - 5 ≠ 0 by intro h'; apply hx4; linarith)]
      ring_nf
    rw [eq8', eq9'] at eq7'
    have eq9 : (x - 6) * (x - 5) * (6 * (x - 6) + 5 * (x - 5)) = (30 : ℝ) * (11 * x - 61) := by
      have eq13 : (x - 6) * (x - 5) * (6 * (x - 6) + 5 * (x - 5)) / (30 : ℝ) = (11 * x - 61) := by
        nlinarith [eq7']
      have eq15 : (x - 6) * (x - 5) * (6 * (x - 6) + 5 * (x - 5)) = (30 : ℝ) * (11 * x - 61) := by
        field_simp at eq13 ⊢
        <;> nlinarith [eq13, sq_pos_of_ne_zero (show x - 6 ≠ 0 by intro h'; apply hx3; linarith), sq_pos_of_ne_zero (show x - 5 ≠ 0 by intro h'; apply hx4; linarith)]
      linarith
    -- First equation factors
    have h3 : x * (5 * x - 13) * (x - 5) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show x - 2 ≠ 0 by intro h'; apply hx1; linarith),
                  sq_pos_of_ne_zero (show x - 3 ≠ 0 by intro h'; apply hx2; linarith)]
    -- Second equation factors
    have h4 : x * (11 * x - 61) * (x - 11) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show x - 6 ≠ 0 by intro h'; apply hx3; linarith),
                  sq_pos_of_ne_zero (show x - 5 ≠ 0 by intro h'; apply hx4; linarith)]
    -- Now we need to show x = 0 is the only common solution.
    cases' (mul_eq_zero.mp h3) with h6 h7
    · cases' (mul_eq_zero.mp h6) with h8 h9
      · -- x = 0
        linarith
      · -- 5 * x - 13 = 0
        have h8' : 5 * x - 13 = 0 := by linarith
        have h10 : x = 13 / 5 := by linarith
        rw [h10] at h4
        norm_num at h4
        all_goals linarith
    · -- x - 5 = 0
      exfalso
      have h10 : x = 5 := by linarith
      have h11 : x ≠ 5 := hx4
      contradiction
  · -- Backward: x = 0 implies both equations
    intro h
    rw [h]
    constructor
    · norm_num
    · norm_num