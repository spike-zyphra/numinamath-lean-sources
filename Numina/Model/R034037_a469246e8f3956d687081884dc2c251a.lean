import Mathlib

open Real

theorem algebra_13977 {x : ℝ}
    (hx : x = ∑ i ∈ Finset.range 2012, sqrt (1 + 1 / ((i + 1)^2) + 1 / ((i + 2)^2))) :
    x - ⌊x⌋ = 2012 / 2013 := by
  have h1 : ∀ (i : ℕ), sqrt (1 + 1 / ((i + 1)^2) + 1 / ((i + 2)^2)) = 1 + 1 / ((i + 1 : ℝ)) - 1 / ((i + 2 : ℝ)) := by
    intro i
    have h2 : (1 + 1 / ((i + 1 : ℝ) ^ 2) + 1 / ((i + 2 : ℝ) ^ 2) : ℝ) = (1 + 1 / ((i + 1 : ℝ)) - 1 / ((i + 2 : ℝ)) ) ^ 2 := by
      field_simp
      ring_nf
    rw [h2]
    have h3 : 0 ≤ (1 + 1 / ((i + 1 : ℝ)) - 1 / ((i + 2 : ℝ)) : ℝ) := by
      have h4 : (1 + 1 / ((i + 1 : ℝ)) - 1 / ((i + 2 : ℝ)) : ℝ) ≥ 0 := by
        have h5 : (i : ℝ) ≥ 0 := by exact_mod_cast (show (i : ℕ) ≥ 0 by omega)
        have h6 : (i + 1 : ℝ) ≥ 1 := by nlinarith
        have h7 : (i + 2 : ℝ) ≥ 2 := by nlinarith
        have h10 : 0 < (↑i + 1 : ℝ) := by nlinarith
        have h11 : 0 < (↑i + 2 : ℝ) := by nlinarith
        have h12 : (1 / ((↑i + 1) : ℝ)) ≥ (1 / ((↑i + 2) : ℝ)) := by
          apply (div_le_div_iff (by nlinarith) (by nlinarith)).mpr
          nlinarith
        nlinarith
      linarith
    rw [Real.sqrt_sq (h3)]
  have h2' : x = ∑ i ∈ Finset.range 2012, (1 + 1 / ((i + 1 : ℝ)) - 1 / ((i + 2 : ℝ)) ) := by
    rw [hx]
    apply Finset.sum_congr
    · rfl
    · intro i hi
      exact h1 i
  have h3 : x = (2013 - (1 : ℝ) / 2013) := by
    rw [h2']
    norm_num
    <;> native_decide
  rw [h3]
  norm_num [Int.floor_eq_iff]