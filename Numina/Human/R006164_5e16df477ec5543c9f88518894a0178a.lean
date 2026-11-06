import Mathlib

/- Let $x$ and $y$ be positive integers not greater than $50$. If $ \sqrt { 24 } < \frac { x } { y } < 5 $, find the value of $x + y$.-/
theorem inequalities_626874 (x y : ℕ) (hx : x ≤ 50) (hy : y ≤ 50) (hxpos : 0 < x) (hypos : 0 < y)
    (hineq : √24 < (x : ℝ) / y ∧ (x : ℝ) / y < 5) : x + y = 59 := by
  obtain ⟨ineq1, ineq2⟩ := hineq
  rw [div_lt_iff₀ (by simpa)] at ineq2
  norm_cast at ineq2
  -- Set k := 5 * y - x
  set k := 5 * y - x with hk
  -- Since x / y ≤ 5, we have 5 * y - x ≥ 0, k ≥ 1. 
  have ineq3 : k ≥ 1 := by omega
  have hk1 : x = 5 * y - k := by omega
  rw [hk1] at ineq1
  rw [lt_div_iff₀ (by simpa)] at ineq1
  -- Note that 2449 / 500 < √24 
  have ineq4 : (2449 / 500) < √24 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have ineq5 : (2449 / 500) * y < √24 * y := by
    gcongr
  -- Then we have 2449 * y < 5 * y - k
  have ineq6 := ineq5.trans ineq1
  rw [Nat.cast_sub (by omega)] at ineq6
  rw [lt_tsub_iff_right] at ineq6
  field_simp at ineq6
  rw [div_lt_iff₀ (by norm_num)] at ineq6
  norm_cast at ineq6
  rw [← lt_tsub_iff_left] at ineq6
  rw [show 5 * y * 500 - 2449 * y = 51 * y by omega] at ineq6
  rw [hk1] at hx
  simp only [tsub_le_iff_right] at hx
  -- By some calculations, 2499 * k ≤ 2550 
  have ineq7 : 2449 * k ≤ 2550 := by omega
  -- Hence, we have k ≤ 1
  have hk4 : k = 1 := by omega
  rw [hk4] at ineq6 hx
  -- Finally, we have y = 10 and x = 49
  have yeq : y = 10 := by omega
  have xeq : x = 49 := by omega
  -- So we have x + y = 59
  rw [yeq, xeq]
