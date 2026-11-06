import Mathlib

open Real

theorem inequalities_147377 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x + y) * (y + z) * (z + x) ≥ 8 * x * y * z ∧
    x^2 + y^2 + z^2 ≥ x * y + y * z + z * x ∧
    x^x * y^y * z^z ≥ (x * y * z)^((x + y + z) / 3) := by

  constructor
  · -- Prove the first inequality: (x + y) * (y + z) * (z + x) ≥ 8 * x * y * z
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x + y + z), mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]

  constructor
  · -- Prove the second inequality: x^2 + y^2 + z^2 ≥ x * y + y * z + z * x
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

  · -- Prove the third inequality: x^x * y^y * z^z ≥ (x * y * z)^((x + y + z) / 3)
    have h1 : x^x * y^y * z^z = Real.exp (x * (Real.log x) + y * (Real.log y) + z * (Real.log z)) := by
      have h2 : x ^x = Real.exp (x * (Real.log x)) := by 
        rw [Real.rpow_def_of_pos hx]
        <;> ring
      have h3 : y ^y = Real.exp (y * (Real.log y)) := by 
        rw [Real.rpow_def_of_pos hy]
        <;> ring
      have h4 : z ^z = Real.exp (z * (Real.log z)) := by 
        rw [Real.rpow_def_of_pos hz]
        <;> ring
      calc
        x ^x * y ^y * z ^z = Real.exp (x * (Real.log x)) * Real.exp (y * (Real.log y)) * Real.exp (z * (Real.log z)) := by 
          rw [h2, h3, h4]
        _ = Real.exp (x * (Real.log x) + y * (Real.log y) + z * (Real.log z)) := by 
          rw [Real.exp_add, Real.exp_add]

    have h2 : (x * y * z)^((x + y + z) / 3) = Real.exp ((x + y + z) / 3 * (Real.log x + Real.log y + Real.log z)) := by
      have h6 : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := by 
        simp [Real.log_mul, hx.ne.symm, hy.ne.symm, hz.ne.symm]
      have h7 : (x * y * z) ^ ((x + y + z) / 3) = Real.exp ((x + y + z) / 3 * (Real.log (x * y * z))) := by 
        rw [Real.rpow_def_of_pos (by positivity)]
        <;> ring
      rw [h6] at h7 
      linarith [h7]

    have h3 : x * (Real.log x) + y * (Real.log y) + z * (Real.log z) ≥ (x + y + z) / 3 * (Real.log x + Real.log y + Real.log z) := by
      have h4 : (x - y) * (Real.log x - Real.log y) ≥ 0 := by
        by_cases hxy : x ≥ y
        · -- Case x ≥ y
          have hln1 : Real.log x ≥ Real.log y := Real.log_le_log (by linarith) (by linarith)
          have hln2 : Real.log x - Real.log y ≥ 0 := by linarith
          have h12 : x - y ≥ 0 := by linarith
          nlinarith [show Real.log x - Real.log y ≥ 0 by linarith, show x - y ≥ 0 by linarith]
        · -- Case y > x
          have hln1 : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) (by linarith)
          have hln2 : Real.log x - Real.log y ≤ 0 := by linarith
          have h12 : x - y < 0 := by linarith
          nlinarith [show Real.log x - Real.log y ≤ 0 by linarith, show x - y < 0 by linarith]

      have h5 : (x - z) * (Real.log x - Real.log z) ≥ 0 := by 
        by_cases hxz : x ≥ z
        · -- Case x ≥ z
          have hln1 : Real.log x ≥ Real.log z := Real.log_le_log (by linarith) (by linarith)
          have hln2 : Real.log x - Real.log z ≥ 0 := by linarith
          have h12 : x - z ≥ 0 := by linarith
          nlinarith [show Real.log x - Real.log z ≥ 0 by linarith, show x - z ≥ 0 by linarith]
        · -- Case z > x
          have hln1 : Real.log x ≤ Real.log z := Real.log_le_log (by linarith) (by linarith)
          have hln2 : Real.log x - Real.log z ≤ 0 := by linarith
          have h12 : x - z < 0 := by linarith
          nlinarith [show Real.log x - Real.log z ≤ 0 by linarith, show x - z < 0 by linarith]

      have h6 : (y - z) * (Real.log y - Real.log z) ≥ 0 := by
        by_cases hyz : y ≥ z
        · -- Case y ≥ z
          have hln1 : Real.log y ≥ Real.log z := Real.log_le_log (by linarith) (by linarith)
          have hln2 : Real.log y - Real.log z ≥ 0 := by linarith
          have h12 : y - z ≥ 0 := by linarith
          nlinarith [show Real.log y - Real.log z ≥ 0 by linarith, show y - z ≥ 0 by nlinarith]
        · -- Case z > y
          have hln1 : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) (by linarith)
          have hln2 : Real.log y - Real.log z ≤ 0 := by linarith
          have h12 : y - z < 0 := by linarith
          nlinarith [show Real.log y - Real.log z ≤ 0 by linarith, show y - z < 0 by linarith]

      nlinarith [h4, h5, h6, mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]

    rw [h1, h2]
    have h4 : Real.exp (x * (Real.log x) + y * (Real.log y) + z * (Real.log z)) ≥ Real.exp ((x + y + z) / 3 * (Real.log x + Real.log y + Real.log z)) := by 
      apply Real.exp_le_exp_of_le 
      linarith [h3]

    linarith [h4]