import Mathlib

theorem algebra_94980 (x y : ℕ) (hx : x ∈ Finset.Icc 10 99) (hy : y ∈ Finset.Icc 10 99)
(hxy : (x + y) = 2 * 60) :
(x / y : ℚ) ≤ 33 / 7 := by
  simp at hx hy
  have h1 : 10 ≤ x := by
    omega
  have h2 : x ≤ 99 := by 
    omega
  have h3 : 10 ≤ y := by
    omega
  have h4 : y ≤ 99 := by
    omega
  have h5 : x + y = 120 := by 
    omega
  have h6 : y ≥ 21 := by
    omega
  have h8 : 7 * x ≤ 33 * y := by 
    omega
  have h9 : (x : ℚ) / (y : ℚ) ≤ 33 / 7 := by
    have h10 : (y : ℚ) > 0 := by
      have h11 : (y : ℚ) ≥ 10 := by
        exact_mod_cast (show (10 : ℕ) ≤ y from by omega)
      linarith
    have h12 : (7 * (x : ℚ) ) ≤ (33 * (y : ℚ) ) := by
      exact_mod_cast (show 7 * x ≤ 33 * y from by omega)
    have h11 : (x : ℚ) / (y : ℚ) ≤ 33 / 7 := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    linarith
  exact_mod_cast h9