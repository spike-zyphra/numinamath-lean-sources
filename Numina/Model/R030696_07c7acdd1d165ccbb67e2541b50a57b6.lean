import Mathlib

theorem inequalities_599009 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a ∈ Set.Icc 1 2) (h2 : b ∈ Set.Icc 1 2) (h3 : c ∈ Set.Icc 1 2) :
    (a + b + c) * (1 / a + 1 / b + 1 / c) ≤ 10 := by 
  rcases h1 with ⟨ha1, ha2⟩
  rcases h2 with ⟨hb1, hb2⟩
  rcases h3 with ⟨hc1, hc2⟩
  have h4 : a + b + c ≥ 3 := by 
    nlinarith
  have h5 : a * b * c > 0 := by
    have ha' : a > 0 := ha
    have hb' : b > 0 := hb
    have hc' : c > 0 := hc
    positivity
  have h7 : (a + b + c) * (1 / a + 1 / b + 1 / c) - 10 ≤ 0 := by
    have pos1 : a * b * c > 0 := by positivity
    have h6 : (a + b + c) * (1 / a + 1 / b + 1 / c) - 10 = 
      ( (a + b + c) * (b * c + a * c + a * b) - 10 * a * b * c ) / (a * b * c) := by
        field_simp
        <;> ring
    rw [h6]
    apply div_nonpos_of_nonpos_of_nonneg
    . -- Show (a + b + c) * (b * c + a * c + a * b) - 10 * a * b * c ≤ 0
      nlinarith [ mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1), 
        mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hc1), 
        mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hc1), 
        mul_nonneg (sub_nonneg.mpr (show 0 ≤ 2 - a by linarith)) (sub_nonneg.mpr (show 0 ≤ 2 - b by linarith)), 
        mul_nonneg (sub_nonneg.mpr (show 0 ≤ 2 - a by linarith)) (sub_nonneg.mpr (show 0 ≤ 2 - c by linarith)), 
        mul_nonneg (sub_nonneg.mpr (show 0 ≤ 2 - b by linarith)) (sub_nonneg.mpr (show 0 ≤ 2 - c by linarith))]
    . -- Show a * b * c ≥ 0
      positivity
  linarith