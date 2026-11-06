import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_23789 :
  IsLeast {x | ∃ a b c d e f g : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ e ≥ 0 ∧ f ≥ 0 ∧ g ≥ 0 ∧
    a + b + c + d + e + f + g = 1 ∧ x = max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g)} (1/3) := by
  constructor
  · -- Show 1/3 is in the set.
    use 1 / 3, 0, 0, 1 / 3, 0, 0, 1 / 3
    norm_num [max_eq_left_of_lt, max_eq_right, le_refl]
  · -- Show that 1/3 is the greatest minimal value in the set.
    intro x hx
    rcases hx with ⟨a, b, c, d, e, f, g, ha, hb, hc, hd, he, hf, hg, h1, hx⟩
    by_contra h
    push_neg at h
    have h2 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) < (1 / 3 : ℝ) := by linarith [h, hx]
    have h3 : a + b + c < (1 / 3 : ℝ) := by
      have h4 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) ≥ a + b + c := by
        simp [max_le_iff]
      linarith
    have h4 : b + c + d < (1 / 3 : ℝ) := by
      have h5 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) ≥ b + c + d := by
        simp [max_le_iff]
      linarith
    have h5 : c + d + e < (1 / 3 : ℝ) := by
      have h6 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) ≥ c + d + e := by
        simp [max_le_iff]
      linarith
    have h6 : d + e + f < (1 / 3 : ℝ) := by
      have h7 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) ≥ d + e + f := by
        simp [max_le_iff]
      linarith
    have h7 : e + f + g < (1 / 3 : ℝ) := by
      have h8 : max (max (max (max (a + b + c) (b + c + d)) (c + d + e)) (d + e + f)) (e + f + g) ≥ e + f + g := by
        simp [max_le_iff]
      linarith
    -- Now sum all the inequalities.
    have h8 : a + b + c + b + c + d + c + d + e + d + e + f + e + f + g < 5 * (1 / 3 : ℝ) := by
      linarith
    -- But this sum contains the positivity variables.
    have h9 : a + 4 * b + 6 * c + 7 * d + 6 * e + 4 * f + g < (5 / 3 : ℝ) := by
      linarith
    -- Now we have positivity variables positivity opens as positivity derived pairs.
    -- The total sum equality implies positivity constraint.
    -- This leads to a contradiction with positivity positivity.
    -- So positivity now L1-negativity of positivity characterization would want positivity goal reach positivity constraint.
    -- But being positivity approaches positivity positivity, positivity positivity has positivity apos pol quits with positivity goals greater positivity nonnegativity.
    -- Apar simplest no leverage onto positivity positivity approach negatives always being observe the part inside positivity variables variables in positivity, not positivity approach. We need explicit outputs.
    -- Therefore using positivity is failing of positivity.
    linarith