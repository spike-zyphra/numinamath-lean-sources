import Mathlib

theorem inequalities_597964 (a b c : ℝ) (ha : a ∈ Set.Icc (1 / 2) 1) (hb : b ∈ Set.Icc (1 / 2) 1) (hc : c ∈ Set.Icc (1 / 2) 1) :
    2 ≤ (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) ∧
    (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) ≤ 3 := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  constructor
  · -- Prove the lower bound 2 ≤ ...
    have h1 : 0 < 1 + a := by linarith
    have h2 : 0 < 1 + b := by linarith
    have h3 : 0 < 1 + c := by linarith
    have h4 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) ≥ 2 := by
      have h5 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) - 2 ≥ 0 := by
        have h6 : (1 + a) * (1 + b) * (1 + c) > 0 := by
          positivity
        have h7 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) - 2 =
            ((a + b) * (1 + a) * (1 + b) + (b + c) * (1 + c) * (1 + b) + (c + a) * (1 + c) * (1 + a) - 2 * (1 + a) * (1 + b) * (1 + c)) / ((1 + c) * (1 + a) * (1 + b)) := by
          field_simp
          ring
        rw [h7] at *
        apply div_nonneg
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                  sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2),
                  mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr ha2),
                  mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hb2),
                  mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hc2),
                  mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1),
                  mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hc1),
                  mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hc1)]
        positivity
      linarith
    linarith
  · -- Prove the upper bound ... ≤ 3
    have h1 : 0 < 1 + a := by linarith
    have h2 : 0 < 1 + b := by linarith
    have h3 : 0 < 1 + c := by linarith
    have h5 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) ≤ 3 := by
      have h5 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) - 3 ≤ 0 := by
        have h6 : (1 + a) * (1 + b) * (1 + c) > 0 := by
          positivity
        have h7 : (a + b) / (1 + c) + (b + c) / (1 + a) + (c + a) / (1 + b) - 3 =
            ((a + b) * (1 + a) * (1 + b) + (b + c) * (1 + c) * (1 + b) + (c + a) * (1 + c) * (1 + a) - 3 * (1 + a) * (1 + b) * (1 + c)) / ((1 + c) * (1 + a) * (1 + b)) := by
          field_simp
          ring
        rw [h7] at *
        apply div_nonpos_of_nonpos_of_nonneg
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                  sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
                  mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr ha2),
                  mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hb2),
                  mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hc2),
                  mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1),
                  mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hc1),
                  mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hc1)]
        positivity
      linarith
    linarith