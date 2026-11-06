import Mathlib

theorem algebra_289189 (a b c d : ℤ) (ha : 0 < a) (hb : a < b) (hc : b < c) (hd : c < d)
    (h1 : d < 10) :
    (a - b : ℝ) / (c - d) ≤ 6 := by 
  have h2 : a ≤ 8 := by
    omega
  have h3 : b ≤ 8 := by
    omega
  have h4 : c ≤ 8 := by
    omega
  have h5 : d ≤ 9 := by
    omega
  have h6 : c - d < 0 := by
    omega 
  have h7 : (a - b : ℝ) / (c - d) ≤ 6 := by
    have h8 : (c - d : ℝ) < 0 := by
      have h9 : (c : ℝ) < (d : ℝ) := by
        exact_mod_cast (show c < d by linarith)
      linarith
    apply (div_le_iff_of_neg' (by linarith)).mpr
    have h9 : a - b ≥ 6 * (c - d) := by 
      omega
    have h10 : (a - b : ℝ) ≥ (6 : ℝ) * (c - d) := by 
      exact_mod_cast h9 
    linarith
  exact h7