import Mathlib 

/- For an arbitrary real number $ x$, $ \lfloor x\rfloor$ denotes the greatest integer not exceeding $ x$. Prove that there is exactly one integer $ m$ which satisfy $ \displaystyle m\minus{}\left\lfloor \frac{m}{2005}\right\rfloor\equal{}2005$. -/
theorem number_theory_69861 :
    ∃! m : ℤ, m - ⌊(m / 2005 : ℝ)⌋ = 2005 := by
  use 2006
  constructor
  · -- Check that 2006 satisfies the equation
    norm_num [Int.subNatNat_eq_coe, Int.cast_ofNat, Int.cast_add, Int.cast_mul]
  · -- Prove that 2006 is the only solution
    intro m h1 
    -- Step 1: Establish Fundamental Relations
    have h4 : ⌊(m / 2005 : ℝ)⌋ ≤ (m / 2005 : ℝ) := Int.floor_le _ 
    have h5 : (m : ℝ) - ⌊(m / 2005 : ℝ)⌋ = (2005 : ℝ) := by
      exact_mod_cast h1
    have hfloor : ⌊(m / 2005 : ℝ)⌋ = (m : ℝ) - (2005 : ℝ) := by
      linarith only [h5]
    have h6 : (m : ℝ) - (2005 : ℝ) ≤ (m : ℝ) / 2005 := by
      rw [hfloor] at h4
      exact h4 
    -- Step 2: Determine Solution Bounds
    -- Lower Bound:
    have h7 : (m : ℝ) > (2005 : ℝ) := by
      have hfloor2 : (m : ℝ) / 2005 < ⌊(m / 2005 : ℝ)⌋ + 1 := by
        apply Int.lt_floor_add_one
      rw [hfloor] at hfloor2
      nlinarith
    have h8 : m ≥ 2006 := by
      rw [ge_iff_le] 
      apply Int.le_of_sub_one_lt 
      exact_mod_cast h7
    -- Upper Bound:
    have h9 : m ≤ 2006 := by
      have h14 : (m : ℝ) - 2005 ≤ (m : ℝ) / 2005 := by
        have hfloor3 : ⌊(m / 2005 : ℝ)⌋ ≤ (m : ℝ) / 2005 := Int.floor_le _
        rw [hfloor] at hfloor3
        exact hfloor3 
      have h15 : (m : ℝ) ≤ (2005 ^ 2 : ℝ) / 2004 := by
        nlinarith [h14]
      norm_num at h15 
      apply Int.le_of_lt_add_one
      suffices (m : ℝ) < 2007 by 
        exact_mod_cast this 
      linarith only [h15]
    exact Int.le_antisymm h9 h8 





