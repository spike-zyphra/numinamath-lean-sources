import Mathlib

/- Evaluate $\left\lceil{\frac32}\right\rceil^2+\left\lceil{\left(\frac32\right)^2}\right\rceil$. -/
theorem algebra_20371 : ⌈(3 / 2 : ℝ)⌉ ^ 2 + ⌈(3 / 2 : ℝ) ^ 2⌉ = 7 := by
  -- Calculate the ceiling of 3/2 = 1.5, which is 2.
  -- we need to prove 1 < 3/2 and 3/2 <= 2 to show ceil(3/2)=2
  -- we can use norm_num tactic to calculate this.
  have h1: ⌈(3 / 2 : ℝ)⌉ = 2 := Int.ceil_eq_iff.2 (And.intro (by norm_num) (by norm_num))
  -- Calculate the square of 3/2, which is 9/4 = 2.25.
  -- obivously, 2<9/4<=3 so ceil((3/2)^2)=3.
  -- we can use norm_num tactic to calculate this too.
  have h2: ⌈(3 / 2 : ℝ) ^ 2⌉ = 3 := Int.ceil_eq_iff.2 (And.intro (by norm_num) (by norm_num))
  -- sub in h1 and h2 to the expression and calculate it.
  rw [h1, h2]
  simp
