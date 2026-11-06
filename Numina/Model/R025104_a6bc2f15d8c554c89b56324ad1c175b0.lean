import Mathlib

open Real

theorem algebra_323088 (x : ℕ → ℝ) (hx1 : x 1 = Real.sqrt 3)
    (hxn : ∀ n, x (n + 1) = (x n + 1) / (1 - x n)) :
    x 1001 - x 401 = 0 := by

  have h1 : ∀ n, x (4 * n + 1) = Real.sqrt 3 := by 
    intro n 
    induction n with
    | zero => 
      norm_num [hx1]
    | succ n ih => 
      have h2 : x (4 * n + 2) = -2 - Real.sqrt 3 := by 
        rw [hxn (4 * n + 1)]
        rw [ih]
        field_simp [(show 1 - Real.sqrt 3 ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show 0 < 3 by norm_num : (3 : ℝ) > (0 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))])]
        <;> ring_nf
        <;> norm_num
        <;> ring
      have h3 : x (4 * n + 3) = (- Real.sqrt 3) / 3 := by 
        rw [hxn (4 * n + 2)]
        rw [h2]
        field_simp [(show 1 - (-2 - Real.sqrt 3) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show 0 < 3 by norm_num : (3 : ℝ) > (0 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))])]
        ring_nf
        <;> field_simp [(show (3 : ℝ) + Real.sqrt 3 ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show 0 < 3 by norm_num : (3 : ℝ) > (0 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))])]
        <;> ring_nf
        <;> norm_num
        <;> ring
      have h4 : x (4 * n + 4) = 2 - Real.sqrt 3 := by 
        rw [hxn (4 * n + 3)]
        rw [h3]
        field_simp [(show 1 - (- Real.sqrt 3 / 3) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show 0 < 3 by norm_num : (3 : ℝ) > (0 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))])]
        ring_nf
        <;> norm_num
        <;> ring
      have h5 : x (4 * (n + 1) + 1) = Real.sqrt 3 := by
        have eq1 : 4 * (n + 1) + 1 = 4 * n + 4 + 1 := by 
          omega
        rw [eq1]
        rw [hxn (4 * n + 4)]
        rw [h4]
        field_simp [(show 1 - (2 - Real.sqrt 3) ≠ 0 by
          nlinarith [Real.sqrt_pos.mpr (show 0 < 3 by norm_num : (3 : ℝ) > (0 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))])]
        ring_nf
        <;> norm_num
        <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
      exact h5
  have h2 : x 1001 = Real.sqrt 3 := by 
    have h3 : ∀ n, x (4 * n + 1) = Real.sqrt 3 := by 
      intro n 
      exact h1 n
    have h4 : 1001 = 4 * (250 : ℕ) + 1 := by 
      omega
    rw [h4]
    apply h3 250
  have h3 : x 401 = Real.sqrt 3 := by 
    have h4 : ∀ n, x (4 * n + 1) = Real.sqrt 3 := by 
      intro n 
      exact h1 n
    have h5 : 401 = 4 * (100 : ℕ) + 1 := by 
      omega
    rw [h5]
    apply h4 100
  rw [h2, h3]
  all_goals norm_num