import Mathlib
/-As shown in Figure 3, a right-angled triangular array of numbers is given, where the numbers in each column form an arithmetic sequence, and from the third row onwards, the numbers in each row form a geometric sequence with equal common ratios. Let the number in the 
i-th row and j-th column be aij (i⩾j,i、j ∈Z +). Then an3 = ?-/
theorem algebra_313892 {a : ℕ → ℕ → ℝ} (ha : ∀ i j, i ≥ j → a i j = a 0 0 + (i - 1) * (1 / 2) ^ j)
    (n : ℕ) : a n 3 = n / 16 := by  
  have h1 := ha 0 0 (by norm_num)
  norm_num at h1