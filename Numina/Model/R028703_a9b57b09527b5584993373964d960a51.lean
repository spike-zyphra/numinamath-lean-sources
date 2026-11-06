import Mathlib

theorem algebra_886 (A B C D E : ℕ) (hA : A ≤ 100) (hB : B ≤ 100) (hC : C ≤ 100) (hD : D ≤ 100)
    (hE : E ≤ 100) (havg : (A + B + C + D + E + (38 - 5) * 62) / (38 : ℝ) = 67) :
    C = 100 := by
  have eq4 : (A + B + C + D + E : ℝ) = 500 := by
    have eq5 : (A + B + C + D + E + (38 - 5) * 62 : ℝ) = 67 * (38 : ℝ) := by
      have eq5 : (A + B + C + D + E + (38 - 5) * 62 : ℝ) / (38 : ℝ) = 67 := by
        simpa using havg
      have eq6 : (A + B + C + D + E + (38 - 5) * 62 : ℝ) = 67 * (38 : ℝ) := by
        field_simp at eq5 ⊢
        linarith
      linarith
    have eq6 : (A + B + C + D + E : ℝ) = 500 := by
      norm_num at eq5 ⊢
      linarith
    exact_mod_cast eq6
  have eq7 : A + B + C + D + E = 500 := by
    exact_mod_cast eq4
  have h1 : C = 100 := by
    omega
  exact h1