import Mathlib

theorem algebra_11323 (q : ℝ → ℝ) (hq : q = fun x => x ^ 4 + 4 * x ^ 2 + 4)
    (domain : Set ℝ) (hd : domain = {x | 0 ≤ x}) :
    ∀ x ∈ domain, 4 ≤ q x ∧ ∀ y, 4 ≤ y → ∃ x ∈ domain, q x = y := by

  have h1 : ∀ x, 0 ≤ x → 4 ≤ q x := by
    intro x hx
    rw [hq]
    have h4 : x ^ 4 + 4 * x ^ 2 + 4 ≥ 4 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 0)]
    simp at *
    all_goals linarith
  intro x hx
  constructor
  · -- Show 4 ≤ q x.
    apply h1
    rw [hd] at hx
    exact hx
  · -- Show ∀ y, 4 ≤ y → ∃ x ∈ domain, q x = y
    intro y hy
    use Real.sqrt (Real.sqrt y - 2)
    constructor
    · -- Show witness is in domain
      rw [hd]
      have h8 : Real.sqrt (Real.sqrt y - 2) ≥ 0 := Real.sqrt_nonneg (Real.sqrt y - 2)
      simp at *
      all_goals nlinarith [ Real.sqrt_nonneg ( Real.sqrt y - 2 ) ]
    · -- Show q x = y
      rw [hq]
      simp
      have h7 : Real.sqrt (Real.sqrt y - 2) ^ 2 = Real.sqrt y - 2 := by
        have h8 : Real.sqrt y - 2 ≥ 0 := by 
          have h5 : y ≥ 4 := by linarith
          have h6 : Real.sqrt y ≥ 2 := by
            have h10 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
              rw [Real.sqrt_eq_cases]
              all_goals norm_num
            have h12 : Real.sqrt y ≥ Real.sqrt (4 : ℝ) := by apply Real.sqrt_le_sqrt; linarith
            nlinarith [ h10, Real.sqrt_nonneg y ]
          nlinarith 
        rw [ Real.sq_sqrt h8 ]
      have h8 : (Real.sqrt (Real.sqrt y - 2) ^ 4) = (Real.sqrt y - 2) ^ 2 := by 
        calc
          Real.sqrt (Real.sqrt y - 2) ^4 = (Real.sqrt (Real.sqrt y - 2) ^ 2) ^ 2 := by ring
          _ = (Real.sqrt y - 2) ^ 2 := by 
            rw [h7]
      nlinarith [ Real.sqrt_nonneg ( Real.sqrt y - 2 ), h7, h8, Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith ) ]