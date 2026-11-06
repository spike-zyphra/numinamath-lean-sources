import Mathlib

theorem inequalities_607623
    (a b c d e : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 1)
    (hb : 0 ≤ b ∧ b ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1)
    (hd : 0 ≤ d ∧ d ≤ 1)
    (he : 0 ≤ e ∧ e ≤ 1) :
    (1 + a + b + c + d + e)^2 ≥ 4 * (a^2 + b^2 + c^2 + d^2 + e^2) := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  rcases hd with ⟨hd1, hd2⟩
  rcases he with ⟨he1, he2⟩
  nlinarith [sq_nonneg (a + b + c + d + e - 1),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (d - 1), sq_nonneg (e - 1),
          mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr ha2),
          mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hb2),
          mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hc2),
          mul_nonneg (sub_nonneg.mpr hd1) (sub_nonneg.mpr hd2),
          mul_nonneg (sub_nonneg.mpr he1) (sub_nonneg.mpr he2)]