import Mathlib

open Real

theorem algebra_9268 (x : ℝ) (hx : 0 < x) (a b : ℝ)
    (ha : a = x + 1) (hb : b = sqrt (x ^ 2 + 7 * x * 1 + 1 ^ 2)) :
    1 < b / a ∧ b / a ≤ 3 / 2 := by
  have ha' : a = x + 1 := ha
  have hb' : b = sqrt (x ^ 2 + 7 * x + 1) := by
    rw [hb]
    ring_nf
  -- Show that $0 < a$ and $0 < b$.
  have h1 : 0 < a := by
    rw [ha']
    linarith
  -- Show that $b > 0$.
  have h2 : b > 0 := by
    rw [hb']
    positivity
  -- Show that $b > a$.
  have h3 : b > a := by
    rw [hb', ha']
    have h4 : sqrt (x ^ 2 + 7 * x + 1) > x + 1 := by
      have h5 : (x + 1) ^ 2 < (x ^ 2 + 7 * x + 1) := by
        nlinarith [sq_pos_of_pos hx]
      have h6 : x + 1 < sqrt (x ^ 2 + 7 * x + 1) := by
        rw [Real.lt_sqrt] <;> nlinarith
      linarith
    linarith
  -- Prove that $1 < b / a$.
  have h4 : 1 < b / a := by
    have h5 : b > a := h3
    apply (lt_div_iff₀ (by linarith)).mpr
    linarith
  -- Prove that $b / a \leq 3 / 2$.
  have h5 : b / a ≤ 3 / 2 := by
    have h6 : b ≤ 3 / 2 * a := by
      rw [hb', ha']
      have h7 : sqrt (x ^ 2 + 7 * x + 1) ≤ (3 / 2) * (x + 1) := by
        have h8 : (x ^ 2 + 7 * x + 1) ≤ ((3 / 2) * (x + 1)) ^ 2 := by
          nlinarith [sq_nonneg (x - 1)]
        have h9 : sqrt (x ^ 2 + 7 * x + 1) ≤ Real.sqrt (((3 / 2) * (x + 1)) ^ 2) := Real.sqrt_le_sqrt h8
        have h10 : Real.sqrt (((3 / 2) * (x + 1)) ^ 2) = (3 / 2) * (x + 1) := by
          rw [Real.sqrt_sq (by positivity)]
        linarith
      linarith
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  constructor
  · exact h4
  · exact h5