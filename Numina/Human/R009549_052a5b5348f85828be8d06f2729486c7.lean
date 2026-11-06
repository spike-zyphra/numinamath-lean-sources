import Mathlib

theorem number_theory_4109 (x : ℤ) 
    (h1 : 3+x ≡ 2^2 [ZMOD 3^3]) 
    (h2 : 5+x ≡ 3^2 [ZMOD 5^3]) 
    (h3 : 7+x ≡ 5^2 [ZMOD 7^3]) : 
    x ≡ 4 [ZMOD 105] := by
  -- deduce x=4 mod 3 from h1
  have h1' : x ≡ 4 [ZMOD 3] := by
    rw [Int.modEq_iff_dvd]
    rw [Int.modEq_iff_add_fac] at h1
    omega
  -- deduce x=4 mod 5 from h2
  have h2' : x ≡ 4 [ZMOD 5] := by
    rw [Int.modEq_iff_dvd]
    rw [Int.modEq_iff_add_fac] at h2
    omega
  -- deduce x=4 mod 7 from h3
  have h3' : x ≡ 4 [ZMOD 7] := by
    rw [Int.modEq_iff_dvd]
    rw [Int.modEq_iff_add_fac] at h3
    omega
  -- combine above results, get x=4 mod 105
  have : x ≡ 4 [ZMOD 3*5] := by
    rw [← Int.modEq_and_modEq_iff_modEq_mul (by norm_num)]
    exact ⟨h1', h2'⟩
  rw [show (105 : ℤ) = 3*5*7 by norm_num]
  rw [← Int.modEq_and_modEq_iff_modEq_mul (by norm_num)]
  exact ⟨this, h3'⟩
