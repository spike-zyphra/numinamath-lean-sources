import Mathlib
 
 /- 2. Solve in the set of integers the equation: $\sqrt{x^{2}-1900}=\left|\frac{x}{4}-4\right|-\sqrt{2017-x^{2}}$.

( Mathematical Gazette ) -/
theorem algebra_113766 {x : ℕ} (hl : 1900 ≤ x^2 ∧ x^2 ≤ 2017) (h : Nat.sqrt (x^2 - 1900) = (x / 4 - 4) - Nat.sqrt (2017 - x^2)) : x = 44 := by
  -- split on the cases x < 44, x = 44, x > 44
  by_cases hlb : x ≤ 43
  -- if x ≤ 43 then x^2 ≤ 1849
  · have : x^2 ≤ 43^2 := Nat.pow_le_pow_left hlb 2
    norm_num at this
    linarith
  · by_cases heq : x = 44
    -- if x = 44 then we are done
    · assumption
    -- if x > 44 then x^2 > 2017
    · rw [show 44 = Nat.succ 43 by norm_num] at heq
      have : x^2 ≥ 45^2 := Nat.pow_le_pow_left (Nat.lt_of_le_of_ne (Nat.gt_of_not_le hlb) (Ne.symm heq)) 2
      norm_num at this
      linarith