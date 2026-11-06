import Mathlib
open Real Set

theorem algebra_4815 : IsGreatest (range (fun x : ℝ => 873 / (x^2 + 14 * x + 58))) 97 := by
  constructor
  · -- Show 97 is in the range.
    use -7
    norm_num
  · -- Show 97 is greatest in the range
    intro y
    rintro ⟨x, hx⟩
    have h1 : x^2 + 14 * x + 58 ≥ 9 := by
      nlinarith [sq_nonneg (x + 7)]
    have h2 : 873 / (x ^ 2 + 14 * x + 58) ≤ 97 := by
      apply (div_le_iff₀ (by nlinarith)).mpr
      nlinarith [h1]
    have h3 : 873 / (x ^ 2 + 14 * x + 58) = y := by
      simpa using hx
    linarith [h3, h2]