import Mathlib

/-Given that a,b and c are all positive numbers not equal to 1, and a^-2 = b ^3= c ^6, then the value of 
abc is 1-/

theorem algebra_326112 {a b c : ℝ} (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1) (hc : 0 < c ∧ c ≠ 1)
    (h1 : a^(-2 : ℤ) = b^(3: ℤ)) (h2 : b^(3: ℤ) = c^(6: ℤ)) : a * b * c = 1 := by
  rw [h2] at h1

  -- express a in terms of c --
  replace h1: a = c ^ (-3 : ℤ) := by
    replace h1: a ^ (2: ℤ) = c ^ (-6: ℤ) := by
      have l:  a ^ (2: ℤ) = (a ^ (-2: ℤ)) ^ (-1: ℤ) := by
         rw [show 2 = -2 * -1 by ring]
         apply zpow_mul
      rw [h1] at l
      rw [l]
      rw [← zpow_mul]
      rw [show 6 * (-1: ℤ) = -6 by ring]
    have o: c ^ (-6:ℤ) = (c ^ (-3: ℤ)) ^ 2 := by
      rw [show -6 = -3 * 2 by ring]
      rw [zpow_mul]
      rfl
    rw [o] at h1
    set A:= a with hA
    set C:= c ^ (-3: ℤ) with hC
    have hl: 0 ≤ A := by
      simp [hA]
      linarith
    have hr: 0 ≤ C := by
      simp [hC]
      norm_cast
      apply pow_nonneg
      linarith
    norm_cast at h1
    rw [sq_eq_sq₀ hl hr] at h1
    exact h1

  -- express b in terms of c --
  replace h2: b = c ^ (2: ℤ) := by
    have o: c ^ (6: ℤ) = (c ^ (2: ℤ)) ^ (3: ℤ) := by
       rw [←zpow_mul]
       rw [show (2: ℤ) * 3 = 6  by ring]
    rw [o] at h2
    norm_cast at h2
    rw [pow_left_inj₀] at h2
    norm_cast
    linarith
    nlinarith
    norm_num

  -- finally, plug them into the expression --
  simp [h1,h2]
  have ne: c ≠ 0 := by nlinarith
  field_simp [ne]
  ring_nf
  norm_cast