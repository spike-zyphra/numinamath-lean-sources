import Mathlib

/- 4. Determine the real values of $x, y, z$, for which


$$

\left\{\begin{array}{l}
\frac{2 x^{2}}{x^{2}+1}=y \\
\frac{3 y^{3}}{y^{4}+y^{2}+1}=z \\
\frac{4 z^{4}}{z^{6}+z^{4}+z^{2}+1}=x
\end{array}\right.

$$
 -/
theorem algebra_108732 {x y z : ℝ} : x ^ 2 + 1 ≠ 0 ∧ y ^ 4 + y ^ 2 + 1 ≠ 0
    ∧ z ^ 6 + z ^ 4 + z ^ 2 + 1 ≠ 0 ∧ 2 * x ^ 2 / (x ^ 2 + 1) = y
    ∧ 3 * y ^ 3 / (y ^ 4 + y ^ 2 + 1) = z ∧ 4 * z ^ 4 / (z ^ 6 + z ^ 4 + z ^ 2 + 1) = x ↔
    x = 0 ∧ y = 0 ∧ z = 0 ∨ x = 1 ∧ y = 1 ∧ z = 1 := by
  constructor
  -- to prove the equations imply the solutions
  . rintro ⟨h1, h2, h3, h4, h5, h6⟩
    -- first of all x, y, z are nonnegative
    have h7 : 0 ≤ x := by rw [← h6]; positivity
    have h8 : 0 ≤ y := by rw [← h4]; positivity
    have h9 : 0 ≤ z := by rw [← h5]; positivity
    -- by am-gm of 2 variables following is true
    have h10 : x ≤ (x^2 + 1) / 2 := by
      have : (0 : ℝ) ≤ 1 / 2 := by norm_num
      convert Real.geom_mean_le_arith_mean2_weighted this this
          (show 0 ≤ x^2 by positivity) (show 0 ≤ 1 by norm_num) (by norm_num) using 1
      . rw [← Real.mul_rpow (by positivity) (by positivity)]
        ring_nf
        rw [show (1 / 2 : ℝ) = (↑(2 : ℕ))⁻¹ by norm_num]
        rw [Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
      . ring
    -- last fact implies y ≤ x as that is implied by the previous inequality
    have h11 : y ≤ x := by
      rw [← h4]
      convert_to x * (x / ((x^2 + 1) / 2)) ≤ x * 1 using 1
      . field_simp; ring
      . ring
      gcongr
      rwa [div_le_one₀ (by positivity)]
    -- by am-gm of 3 variables following is true
    have h12 : y^2 ≤ (y^4 + y^2 + 1) / 3 := by
      have : (0 : ℝ) ≤ 1 / 3 := by norm_num
      convert Real.geom_mean_le_arith_mean3_weighted this this this
          (show 0 ≤ y^4 by positivity) (show 0 ≤ y^2 by positivity) (show 0 ≤ 1 by norm_num)
          (by norm_num) using 1
      . repeat rw [← Real.mul_rpow (by positivity) (by positivity)]
        ring_nf
        rw [show y^6 = (y^2)^3 by ring]
        rw [show (1 / 3 : ℝ) = (↑(3 : ℕ))⁻¹ by norm_num]
        rw [Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
      . ring
    -- z ≤ y as this is result of last inequality
    have h13 : z ≤ y := by
      rw [← h5]
      convert_to y * (y^2 / ((y^4 + y^2 + 1) / 3)) ≤ y * 1 using 1
      . field_simp; ring
      . ring
      gcongr
      rwa [div_le_one₀ (by positivity)]
    -- following is true due to am-gm of 4 variables
    have h14 : z^3 ≤ (z^6 + z^4 + z^2 + 1) / 4 := by
      have : (0 : ℝ) ≤ 1 / 4 := by norm_num
      convert Real.geom_mean_le_arith_mean4_weighted this this this this
          (show 0 ≤ z^6 by positivity) (show 0 ≤ z^4 by positivity) (show 0 ≤ z^2 by positivity) (show 0 ≤ 1 by norm_num)
          (by norm_num) using 1
      . repeat rw [← Real.mul_rpow (by positivity) (by positivity)]
        ring_nf
        rw [show z^12 = (z^3)^4 by ring]
        rw [show (1 / 4 : ℝ) = (↑(4 : ℕ))⁻¹ by norm_num]
        rw [Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
      . ring
    -- x ≤ z is a reslt of previous inequality
    have h15 : x ≤ z := by
      rw [← h6]
      convert_to z * (z^3 / ((z^6 + z^4 + z^2 + 1) / 4)) ≤ z * 1 using 1
      . field_simp; ring
      . ring
      gcongr
      rwa [div_le_one₀ (by positivity)]
    -- x ≤ y ≤ z ≤ x imples x = y = z
    have h16 : x = y := by linarith
    have h18 : x = z := by linarith
    -- pluggin in y = x at first equation gives x * (x - 1) ^2 = 0
    rw [← h16] at h4
    field_simp at h4
    replace h4 : 0 = x * (x - 1)^2 := by linear_combination h4
    rw [eq_comm] at h4
    simp at h4
    -- so x = 0 or x = 1, from this we get our target equalities
    obtain hx | hx := h4
    . left
      and_intros <;> linarith
    . right
      and_intros <;> linarith
  -- to prove x = 0, 1 are solutions, just plug in and calculate
  . rintro h
    obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := h
    . norm_num
    . norm_num