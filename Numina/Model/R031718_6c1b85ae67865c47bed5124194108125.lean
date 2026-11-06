import Mathlib

open Real

theorem algebra_212863 (m n a : ℝ) (hm : 0 < m) (hn : 0 < n) (ha : 0 < a ∧ a ≠ 1) :
    logb a ((m ^ 4 * n ^ (-4 : ℤ) / (m ^ (-1 : ℤ) * n)) ^ (-3 : ℤ) /
      ((m ^ (-2 : ℤ) * n ^ 2) / (m * n ^ (-1 : ℤ))) ^ 5) = 0 := by

  have ha1 : 0 < a := ha.1
  have ha2 : a ≠ 1 := ha.2

  have h1 : (m ^ 4 * n ^ (-4 : ℤ) / (m ^ (-1 : ℤ) * n)) ^ (-3 : ℤ) =
          m ^ (-15 : ℤ) * n ^ (15 : ℤ) := by
    simp [zpow_neg, zpow_ofNat, mul_comm]
    <;> field_simp [hm.ne', hn.ne']
    <;> ring

  have h2 : ((m ^ (-2 : ℤ) * n ^ 2) / (m * n ^ (-1 : ℤ))) ^ 5 =
          m ^ (-15 : ℤ) * n ^ (15 : ℤ) := by 
    simp [zpow_neg, zpow_ofNat, mul_comm]
    <;> field_simp [hm.ne', hn.ne']
    <;> ring

  have h3 : ((m ^ 4 * n ^ (-4 : ℤ) / (m ^ (-1 : ℤ) * n)) ^ (-3 : ℤ) /
      ((m ^ (-2 : ℤ) * n ^ 2) / (m * n ^ (-1 : ℤ))) ^ 5) = 1 := by
    rw [h1, h2]
    have h4 : m ^ (-15 : ℤ) * n ^ (15 : ℤ) ≠ 0 := by
      have hm15 : m ^ (-15 : ℤ) ≠ 0 := by
        have hm' : m ≠ 0 := by linarith
        have : m ^ (-15 : ℤ) = (m ^ 15)⁻¹ := by
          rw [zpow_neg, zpow_ofNat]
        rw [this]
        apply inv_ne_zero
        apply pow_ne_zero 15
        exact hm'
      have hn15 : n ^ (15 : ℤ) ≠ 0 := by
        have hn' : n ≠ 0 := by linarith
        have : n ^ (15 : ℤ) = n ^ 15 := by
          norm_cast
        rw [this]
        apply pow_ne_zero 15
        exact hn'
      apply mul_ne_zero
      exact hm15
      exact hn15
    field_simp [h4]

  rw [h3]
  simp [logb_one]