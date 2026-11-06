import Mathlib

open Real

theorem algebra_300424 : 50 * ⌊2 * (∑ i ∈ Finset.range 1002, (1 / (sqrt (2 * i + 1) + sqrt (2 * i + 3))))⌋ - 142 = 2008 := by 
  have h1 : ∀ (i : ℕ), 1 / (sqrt (2 * (i : ℝ) + 1) + sqrt (2 * (i : ℝ) + 3)) = (sqrt (2 * (i : ℝ) + 3) - sqrt (2 * (i : ℝ) + 1)) / 2 := by 
    intro i
    have h1 : sqrt (2 * (i : ℝ) + 1) > 0 := by 
      apply Real.sqrt_pos.mpr
      linarith 
    have h2 : sqrt (2 * (i : ℝ) + 3) > 0 := by 
      apply Real.sqrt_pos.mpr 
      linarith 
    field_simp [(show sqrt (2 * (i : ℝ) + 1) + sqrt (2 * (i : ℝ) + 3) ≠ 0 by linarith [h1, h2])]
    nlinarith [Real.sqrt_nonneg (2 * (i : ℝ) + 1), Real.sqrt_nonneg (2 * (i : ℝ) + 3),
      sq_nonneg (sqrt (2 * (i : ℝ) + 1) - sqrt (2 * (i : ℝ) + 3)), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 * (i : ℝ) + 1 by nlinarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 * (i : ℝ) + 3 by nlinarith), 
      mul_nonneg (Real.sqrt_nonneg (2 * (i : ℝ) + 1)) (Real.sqrt_nonneg (2 * (i : ℝ) + 3)), 
      sq_nonneg (sqrt (2 * (i : ℝ) + 1) + sqrt (2 * (i : ℝ) + 3))
    ]
  have h2 : (∑ i ∈ Finset.range 1002, (1 / (sqrt (2 * (i : ℝ) + 1) + sqrt (2 * (i : ℝ) + 3)))) = (sqrt (2005) - 1) / 2 := by
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    have h3 : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((sqrt (2 * (i : ℝ) + 3) - sqrt (2 * (i : ℝ) + 1)) / 2) = (sqrt (2 * (n : ℝ) + 1) - 1) / 2 := by
      intro n
      induction n with 
      | zero =>
        simp 
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp 
        <;> ring_nf <;> simp [Real.sqrt_pos.mpr] 
        <;> nlinarith [Real.sqrt_nonneg (2 * (n : ℝ) + 1), Real.sqrt_nonneg (2 * (n : ℝ) + 3), Real.sqrt_nonneg (2 * (n : ℝ) + 1 + 2), Real.sqrt_nonneg (2 * (n : ℝ) + 3 + 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (n : ℝ) + 1) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (n : ℝ) + 3) by nlinarith)]
    specialize h3 1002 
    norm_num at h3 ⊢ 
    <;> nlinarith 
  rw [h2]
  have h3 : ⌊2 * ((sqrt (2005) - 1) / 2)⌋ = 43 := by
    have h4 : 44 < sqrt (2005 : ℝ) := by 
      rw [Real.lt_sqrt] <;> norm_num 
    have h5 : sqrt (2005 : ℝ) < 45 := by 
      rw [Real.sqrt_lt] <;> norm_num 
    have h6 : 43 < sqrt (2005 : ℝ) - 1 := by 
      nlinarith 
    have h7 : sqrt (2005 : ℝ) - 1 < 44 := by 
      nlinarith 
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith 
  rw [h3]
  all_goals norm_num