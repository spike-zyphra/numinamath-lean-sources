import Mathlib

theorem algebra_318767 {x y z : ℤ} (h1 : abs (x + y) + abs (y + z) + abs (z + x) = 4)
    (h2 : abs (x - y) + abs (y - z) + abs (z - x) = 2) :
    x^2 + y^2 + z^2 = 2 := by
  have h3 : x ≤ 2 := by
    cases' abs_cases (x + y) with hxy hxy <;> 
      cases' abs_cases (y + z) with hyz hyz <;> 
        cases' abs_cases (z + x) with hzx hzx <;> 
          cases' abs_cases (x - y) with hxy' hxy' <;> 
            cases' abs_cases (y - z) with hyz' hyz' <;> 
              cases' abs_cases (z - x) with hzx' hzx' <;> 
                omega
  have h4 : x ≥ -2 := by 
    cases' abs_cases (x + y) with hxy hxy <;> 
      cases' abs_cases (y + z) with hyz hyz <;> 
        cases' abs_cases (z + x) with hzx hzx <;> 
          cases' abs_cases (x - y) with hxy' hxy' <;> 
            cases' abs_cases (y - z) with hyz' hyz' <;> 
              cases' abs_cases (z - x) with hzx' hzx' <;> 
                omega
  have h5 : y ≤ 2 := by 
    cases' abs_cases (x + y) with hxy hxy <;> 
      cases' abs_cases (y + z) with hyz hyz <;> 
        cases' abs_cases (z + x) with hzx hzx <;> 
          cases' abs_cases (x - y) with hxy' hxy' <;> 
            cases' abs_cases (y - z) with hyz' hyz' <;> 
              cases' abs_cases (z - x) with hzx' hzx' <;> 
                omega
  have h6 : y ≥ -2 := by 
    cases' abs_cases (x + y) with hxy hxy <;> 
      cases' abs_cases (y + z) with hyz hyz <;> 
        cases' abs_cases (z + x) with hzx hzx <;> 
          cases' abs_cases (x - y) with hxy' hxy' <;> 
            cases' abs_cases (y - z) with hyz' hyz' <;> 
              cases' abs_cases (z - x) with hzx' hzx' <;> 
                omega
  have h7 : z ≤ 2 := by 
    cases' abs_cases (x + y) with hxy hxy <;> 
      cases' abs_cases (y + z) with hyz hyz <;> 
        cases' abs_cases (z + x) with hzx hzx <;> 
          cases' abs_cases (x - y) with hxy' hxy' <;> 
            cases' abs_cases (y - z) with hyz' hyz' <;> 
              cases' abs_cases (z - x) with hzx' hzx' <;> 
                omega
  have h8 : z ≥ -2 := by 
    cases' abs_cases (x + y) with hxy hxy <;> 
      cases' abs_cases (y + z) with hyz hyz <;> 
        cases' abs_cases (z + x) with hzx hzx <;> 
          cases' abs_cases (x - y) with hxy' hxy' <;> 
            cases' abs_cases (y - z) with hyz' hyz' <;> 
              cases' abs_cases (z - x) with hzx' hzx' <;> 
                omega
  interval_cases x <;> interval_cases y <;> interval_cases z 
    <;> norm_num at h1 h2 ⊢ 
    <;> omega