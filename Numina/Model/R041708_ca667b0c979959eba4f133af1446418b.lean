import Mathlib
open Real

theorem algebra_97967 (x y z r : ℝ) (hy : y = x * r) (hz : z = x * r^2) (hn : x ≠ y)
(h : 2 * 2 * y = x + 3 * z) : r = 1 / 3 := by
  have h3 : 4 * y = x + 3 * z := by
    linarith
  rw [hy] at h3
  rw [hz] at h3
  have h4 : x * (3 * r^2 - 4 * r + 1) = 0 := by
    nlinarith 
    <;> nlinarith 
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- case x = 0, which contradicts x ≠ y
    have hx0 : x = 0 := by 
      linarith
    have hy0 : y = 0 := by
      rw [hy]
      rw [hx0]
      norm_num
    have hxy : x = y := by
      linarith [hx0, hy0]
    tauto
  · -- solve quadratic equation 3 * r^2 - 4 * r + 1 = 0
    have hquadratic : 3 * r^2 - 4 * r + 1 = 0 := by
      nlinarith 
    have hfactored : (3 * r - 1) * (r - 1) = 0 := by
      nlinarith [hquadratic]
    cases' (mul_eq_zero.mp hfactored) with h7 h8
    · -- r = 1/3
      linarith 
    · -- r = 1, which contradicts x ≠ y
      have hr1 : r = 1 := by
        linarith
      have h7 : y = x := by 
        rw [hy]
        rw [hr1]
        all_goals 
          ring_nf 
      have hne : x = y := by 
        linarith [h7]
      tauto