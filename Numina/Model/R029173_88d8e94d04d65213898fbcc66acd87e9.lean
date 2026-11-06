import Mathlib

theorem number_theory_110355 {a b : ℤ} (h : a + b ≡ 0 [ZMOD 3]) :
    a^3 + b^3 ≡ 0 [ZMOD 9] := by 
  norm_num [Int.ModEq] at h ⊢
  have h1 : a + b = 3 * ((a + b) / 3) := by 
    omega
  have h2 : a^3 + b^3 = (a + b)^3 - 3 * (a * b) * (a + b) := by
    ring
  rw [h2, h1]
  have h4 : ((3 * ((a + b) / 3)) ^ 3 - 3 * (a * b) * (3 * ((a + b) / 3))) % 9 = 0 := by
    have eq1 : (3 * ((a + b) / 3)) ^ 3 % 9 = 0 := by
      have h5 : (3 * ((a + b) / 3)) % 9 = 0 ∨ (3 * ((a + b) / 3)) % 9 = 3 ∨ (3 * ((a + b) / 3)) % 9 = 6 := by 
        omega
      rcases h5 with (h5 | h5 | h5)
      · -- If (3 * k) % 9 = 0
        simp [h5, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        <;> omega
      · -- If (3 * k) % 9 = 3
        simp [h5, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        <;> omega
      · -- If (3 * k) % 9 = 6
        simp [h5, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        <;> omega
    have eq2 : (3 * (a * b) * (3 * ((a + b) / 3))) % 9 = 0 := by
      have eq3 : (3 * (a * b) * (3 * ((a + b) / 3))) = 9 * (a * b * ((a + b) / 3)) := by 
        ring
      rw [eq3]
      simp [Int.mul_emod]
      all_goals omega
    omega
  omega