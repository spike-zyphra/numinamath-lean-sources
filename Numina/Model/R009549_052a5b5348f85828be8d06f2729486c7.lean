import Mathlib

theorem number_theory_4109 (x : ℤ) 
    (h1 : 3+x ≡ 2^2 [ZMOD 3^3]) 
    (h2 : 5+x ≡ 3^2 [ZMOD 5^3]) 
    (h3 : 7+x ≡ 5^2 [ZMOD 7^3]) : 
    x ≡ 4 [ZMOD 105] := by
  norm_num [Int.ModEq] at h1 h2 h3 ⊢
  omega