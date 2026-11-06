import Mathlib

theorem algebra_262178 {f : ℝ → ℝ} (hf : f = fun x => x^2 - 3 * x + 2) :
    Set.ncard {x | f (f x) = 0} = 4 := by
  have h1 : {x | f (f x) = 0} = {0, 3, (3 + Real.sqrt 5) / 2, (3 - Real.sqrt 5) / 2} := by
    ext x
    simp [hf]
    constructor
    · -- Assume f(f(x)) = 0, prove x in the set
      intro h
      have h2 : (x ^ 2 - 3 * x + 2) ^ 2 - 3 * (x ^ 2 - 3 * x + 2) + 2 = 0 := by
        ring_nf at h ⊢
        nlinarith
      have h3 : (x ^ 2 - 3 * x + 2 - 1) * (x ^ 2 - 3 * x + 2 - 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h3) with h4 h5
      · -- First case
        have h6 : x ^ 2 - 3 * x + 1 = 0 := by 
          nlinarith
        have h7 : (x - (3 + Real.sqrt 5) / 2) * (x - (3 - Real.sqrt 5) / 2) = 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 5 by norm_num : (0:ℝ) < 5), 
          Real.sq_sqrt (show (0:ℝ) ≤ (5:ℝ) by norm_num : (0:ℝ) ≤ (5:ℝ)), 
          Real.sqrt_pos.mpr (show (0:ℝ) < 5 by norm_num : (0:ℝ) < 5)]
        cases' (mul_eq_zero.mp h7) with h8 h9
        · -- First root
          right
          right
          left
          linarith
        · -- Second root
          right
          right
          right
          linarith
      · -- Second case
        have h8 : x * (x - 3) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h8) with h9 h10
        · -- First root
          left
          linarith
        · -- Second root
          right
          left
          linarith
    · -- Assume x in the set, prove f(f(x)) = 0
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 0
        norm_num [hf]
      · -- x = 3
        norm_num [hf]
      · -- x = (3 + √5) / 2
        norm_num [hf]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 5 by norm_num : (0:ℝ) < 5), 
        Real.sq_sqrt (show (0:ℝ) ≤ (5:ℝ) by norm_num : (0:ℝ) ≤ (5:ℝ)), 
        Real.sqrt_pos.mpr (show (0:ℝ) < 5 by norm_num : (0:ℝ) < 5)]
      · -- x = (3 - √5) / 2
        norm_num [hf]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 5 by norm_num : (0:ℝ) < 5), 
        Real.sq_sqrt (show (0:ℝ) ≤ (5:ℝ) by norm_num : (0:ℝ) ≤ (5:ℝ)), 
        Real.sqrt_pos.mpr (show (0:ℝ) < 5 by norm_num : (0:ℝ) < 5)]
  rw [h1]
  have h2 : (0 : ℝ) ≠ 3 := by norm_num
  have h5_ne1 : (0 : ℝ) ≠ (3 + Real.sqrt 5) / 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h6_ne1 : (0 : ℝ) ≠ (3 - Real.sqrt 5) / 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h7 : (3 : ℝ) ≠ (3 + Real.sqrt 5) / 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h8 : (3 : ℝ) ≠ (3 - Real.sqrt 5) / 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h9 : ( (3 + Real.sqrt 5) / 2 : ℝ) ≠ ( (3 - Real.sqrt 5) / 2 : ℝ) := by
    intro h
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num)]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton, h2, h5_ne1, h6_ne1, h7, h8, h9]
  all_goals
    try { 
      norm_num 
      <;> linarith 
      <;> tauto 
    }