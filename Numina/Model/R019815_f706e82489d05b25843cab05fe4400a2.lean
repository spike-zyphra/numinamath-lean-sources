import Mathlib

theorem inequalities_69218 (a b c d e : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1) (he : 0 ≤ e ∧ e ≤ 1) :
    (1 + a + b + c + d + e)^2 ≥ 4 * (a^2 + b^2 + c^2 + d^2 + e^2) := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  rcases hc with ⟨hc0, hc1⟩
  rcases hd with ⟨hd0, hd1⟩
  rcases he with ⟨he0, he1⟩
  nlinarith [sq_nonneg (a + b + c + d + e - 1), sq_nonneg (a + b + c + d + e - 2),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e),
          sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e),
          sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (d - e),
          mul_nonneg (sub_nonneg.mpr ha0) (sub_nonneg.mpr ha1),
          mul_nonneg (sub_nonneg.mpr hb0) (sub_nonneg.mpr hb1),
          mul_nonneg (sub_nonneg.mpr hc0) (sub_nonneg.mpr hc1),
          mul_nonneg (sub_nonneg.mpr hd0) (sub_nonneg.mpr hd1),
          mul_nonneg (sub_nonneg.mpr he0) (sub_nonneg.mpr he1)]