import Mathlib

/- Which number is larger,


$$

1997^{1998^{1999}} \quad \text { or } \quad 1999^{1998^{1997}} ?

$$
 -/
theorem number_theory_222452 : (1997^(1998^1999 : ℕ)) > (1999^(1998^1997 : ℕ)) := by

  have h0 : 1997^1998^1999 = (1997^1998^2)^1998^1997 := by
    rw [← pow_mul, ← pow_add]
    
  --1997^1998^2 > 1999
  have h1 : 1997^1998^2 > 1999 := by
    apply lt_of_lt_of_le (b := 1997^(2^2))
    · norm_num
    · apply pow_le_pow_right₀ (by norm_num)
      norm_num

  -- Finally...
  rw [h0]
  apply pow_lt_pow_left₀ h1
  norm_num
  norm_num