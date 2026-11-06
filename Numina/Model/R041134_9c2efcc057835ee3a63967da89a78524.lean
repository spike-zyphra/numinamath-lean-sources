import Mathlib

theorem inequalities_66865 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) ≤ (1 / 3) * Real.sqrt ((a ^ 2 + b ^ 2) / 2) +
    (2 / 3) * (2 / (1 / a + 1 / b)) := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : Real.sqrt (a * b) ≥ 0 := by positivity
  have h3 : (1 / a + 1 / b) = (a + b) / (a * b) := by
    field_simp
    <;> ring
  have h4 : (2 / 3) * (2 / (1 / a + 1 / b)) = (4 * (a * b)) / (3 * (a + b)) := by
    rw [h3]
    field_simp
    <;> ring
  rw [h4]
  have h5 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) ≥ 0 := by positivity
  have h7 : 0 < a + b := by linarith
  suffices Real.sqrt (a * b) ≤ (1 / 3) * Real.sqrt ((a ^ 2 + b ^ 2) / 2) + (4 * (a * b)) / (3 * (a + b)) by linarith
  have h8 : Real.sqrt (a * b) ≤ (1 / 3) * Real.sqrt ((a ^ 2 + b ^ 2) / 2) + (4 * (a * b)) / (3 * (a + b)) := by
    have h100 : Real.sqrt (a * b) * (3 * (a + b)) ≤ (a + b) * Real.sqrt ((a ^ 2 + b ^ 2) / 2) + 4 * (a * b) := by
      have h100 : 0 ≤ ( (a + b) * Real.sqrt ((a ^ 2 + b ^ 2) / 2) + 4 * (a * b) - Real.sqrt (a * b) * (3 * (a + b)) ) := by
        have h170 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) ≥ Real.sqrt (a * b) := by
          apply Real.sqrt_le_sqrt
          nlinarith [sq_nonneg (a - b)]
        have h700 : (Real.sqrt ((a ^ 2 + b ^ 2) / 2)) ^ 2 ≥ (Real.sqrt (a * b)) ^ 2 := by
          have h1000 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) ≥ Real.sqrt (a * b) := by
            apply Real.sqrt_le_sqrt
            nlinarith [sq_nonneg (a - b)]
          have h1010 : (Real.sqrt ((a ^ 2 + b ^ 2) / 2)) ^ 2 = (a ^ 2 + b ^ 2) / 2 := Real.sq_sqrt (by positivity)
          have h1020 : (Real.sqrt (a * b)) ^ 2 = a * b := Real.sq_sqrt (by positivity)
          nlinarith
        have h200 : ( (a + b) * Real.sqrt ((a ^ 2 + b ^ 2) / 2) + 4 * (a * b) - Real.sqrt (a * b) * (3 * (a + b)) ) ≥ 0 := by
          have h1010 : (Real.sqrt (a * b)) ^ 2 = a * b := Real.sq_sqrt (by positivity)
          have h1020 : (Real.sqrt ((a ^ 2 + b ^ 2) / 2)) ^ 2 = (a ^ 2 + b ^ 2) / 2 := Real.sq_sqrt (by positivity)
          nlinarith [sq_nonneg (Real.sqrt (a * b) - Real.sqrt ((a ^ 2 + b ^ 2) / 2)), 
                sq_nonneg (a - b), 
                Real.sqrt_nonneg (a * b), 
                Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), 
                sq_nonneg ( (a + b) * Real.sqrt ((a ^ 2 + b ^ 2) / 2) - 4 * (a * b) ), 
                sq_nonneg ( Real.sqrt (a * b) * (3 * (a + b)) - (a + b) * Real.sqrt ((a ^ 2 + b ^ 2) / 2) ), 
                mul_nonneg (Real.sqrt_nonneg (a * b)) (Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2)), 
                Real.sq_sqrt (show (0 : ℝ) ≤ (a * b) by positivity), 
                Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2) / 2 by positivity), 
                mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith) 
            ]
        linarith
      linarith
    have h101 : Real.sqrt (a * b) ≤ (1 / 3) * Real.sqrt ((a ^ 2 + b ^ 2) / 2) + (4 * (a * b)) / (3 * (a + b)) := by
      have h102 : 0 < 3 * (a + b) := by positivity
      have h103 : Real.sqrt (a * b) * (3 * (a + b)) ≤ (a + b) * Real.sqrt ((a ^ 2 + b ^ 2) / 2) + 4 * (a * b) := h100
      have h104 : Real.sqrt (a * b) ≤ ( (a + b) * Real.sqrt ((a ^ 2 + b ^ 2) / 2) + 4 * (a * b) ) / (3 * (a + b)) := by
        apply (le_div_iff₀ (by positivity)).mpr
        linarith
      have h105 : ( (a + b) * Real.sqrt ((a ^ 2 + b ^ 2) / 2) + 4 * (a * b) ) / (3 * (a + b)) = (1 / 3) * Real.sqrt ((a ^ 2 + b ^ 2) / 2) + (4 * (a * b)) / (3 * (a + b)) := by
        field_simp
        <;> ring
      rw [h105] at h104
      linarith
    linarith
  linarith