import Mathlib

theorem algebra_271223 {x y z : ℝ} (h1 : |1 - x| = y + 1) (h2 : |1 + y| = z - 2)
    (h3 : |2 - z| = x - x ^ 2) :
    (x, y, z) = (1, -1, 2) := by

  have h1_nonneg : y + 1 ≥ 0 := by
    linarith [abs_nonneg (1 - x), h1]
  
  by_cases h11 : 1 - x ≥ 0
  · -- Case 1: 1 - x ≥ 0, so |1 - x| = 1 - x
    have h1_eq : 1 - x = y + 1 := by 
      rw [abs_of_nonneg h11] at h1 
      linarith 
    have hp1 : y = -x := by linarith 
    have h111 : z = 3 - x := by 
      have h21 : |1 + y| = z - 2 := h2 
      rw [hp1] at h21 
      have h211 : |1 + (-x)| = z - 2 := h21 
      have h1111 : 1 + (-x) = (1 - x) := by ring_nf 
      rw [h1111] at h211 
      rw [abs_of_nonneg (show (1 - x : ℝ) ≥ 0 by linarith [h11])] at h211 
      linarith 
    have h31 : |2 - z| = x - x ^ 2 := h3 
    rw [show z = 3 - x by linarith [h111]] at h31 
    by_cases h1111 : 2 - (3 - x) ≥ 0 
    · -- Case 1a: 2 - (3 - x) ≥ 0, so x ≤ 1.
      rw [abs_of_nonneg h1111] at h31 
      have hx1 : x = 1 := by nlinarith 
      have hy1 : y = -1 := by linarith [hp1, hx1] 
      have hz1 : z = 2 := by linarith [h111, hx1] 
      simp [hx1, hy1, hz1] 
      <;> norm_num [hx1, hy1, hz1] 
    · -- Case 1b: 2 - (3 - x) < 0 
      rw [abs_of_neg (show 2 - (3 - x) < 0 by linarith)] at h31 
      nlinarith 
  · -- Case 2: 1 - x < 0, so |1 - x| = x - 1
    have h1_eq : x - 1 = y + 1 := by 
      rw [abs_of_neg (show 1 - x < 0 by linarith)] at h1 
      linarith 
    have hp2 : y = x - 2 := by linarith 
    have h22 : z = x + 1 := by 
      have h21 : |1 + y| = z - 2 := h2 
      rw [hp2] at h21 
      have h211 : |1 + (x - 2)| = z - 2 := h21 
      have h2111 : 1 + (x - 2) = x - 1 := by ring_nf 
      rw [h2111] at h211 
      have h1111 : x - 1 > 0 := by linarith 
      rw [abs_of_pos h1111] at h211 
      linarith 
    have h32 : |2 - z| = x - x ^ 2 := h3 
    rw [show z = x + 1 by linarith [h22]] at h32 
    by_cases h3333 : 2 - (x + 1) ≥ 0 
    · -- Case 2a: |2 - (x + 1)| = 2 - (x + 1)
      rw [abs_of_nonneg h3333] at h32 
      nlinarith 
    · -- Case 2b: |2 - (x + 1)| = (x + 1) - 2 
      rw [abs_of_neg (show 2 - (x + 1) < 0 by linarith)] at h32 
      nlinarith