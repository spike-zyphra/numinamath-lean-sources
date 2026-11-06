import Mathlib

theorem inequalities_268408 (p q r s : ℝ) (hpqr : p > 0 ∧ q > 0 ∧ r > 0 ∧ s > 0) :
    81 ≤ ((p^2 + p + 1) * (q^2 + q + 1) * (r^2 + r + 1) * (s^2 + s + 1)) / (p * q * r * s) := by
  rcases hpqr with ⟨hp, hq, hr, hs⟩
  have hp1 : p * q * r * s > 0 := by
    apply mul_pos
    apply mul_pos
    apply mul_pos
    exact hp
    exact hq
    exact hr
    exact hs
  have h2 : ((p^2 + p + 1) * (q^2 + q + 1) * (r^2 + r + 1) * (s^2 + s + 1)) ≥ 81 * (p * q * r * s) := by
    have hp2 : p^2 + p + 1 ≥ 3 * p := by
      nlinarith [sq_nonneg (p - 1)]
    have hq2 : q^2 + q + 1 ≥ 3 * q := by
      nlinarith [sq_nonneg (q - 1)]
    have hr2 : r^2 + r + 1 ≥ 3 * r := by
      nlinarith [sq_nonneg (r - 1)]
    have hs2 : s^2 + s + 1 ≥ 3 * s := by
      nlinarith [sq_nonneg (s - 1)]
    have h3 : (p^2 + p + 1) * (q^2 + q + 1) ≥ 9 * (p * q) := by
      nlinarith [mul_pos hp hq, hp2, hq2]
    have h4 : (r^2 + r + 1) * (s^2 + s + 1) ≥ 9 * (r * s) := by
      nlinarith [mul_pos hr hs, hr2, hs2]
    have h5 : ((p^2 + p + 1) * (q^2 + q + 1) * (r^2 + r + 1) * (s^2 + s + 1)) ≥ (81 * (p * q * r * s)) := by
      have h6 : ((p^2 + p + 1) * (q^2 + q + 1)) * ((r^2 + r + 1) * (s^2 + s + 1)) ≥ (9 * (p * q)) * (9 * (r * s)) := by
        apply mul_le_mul
        exact h3
        exact h4
        all_goals
        positivity
      have h7 : (9 * (p * q)) * (9 * (r * s)) = 81 * (p * q * r * s) := by
        ring
      have h8 : ((p^2 + p + 1) * (q^2 + q + 1) * (r^2 + r + 1) * (s^2 + s + 1)) = ((p^2 + p + 1) * (q^2 + q + 1)) * ((r^2 + r + 1) * (s^2 + s + 1)) := by ring
      rw [h8] at *
      linarith [h6, h7]
    linarith
  have h7 : ((p^2 + p + 1) * (q^2 + q + 1) * (r^2 + r + 1) * (s^2 + s + 1)) / (p * q * r * s) ≥ 81 := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  linarith [h7]