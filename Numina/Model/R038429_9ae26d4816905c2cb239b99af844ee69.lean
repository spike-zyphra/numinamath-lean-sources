import Mathlib

theorem number_theory_6287 :
    ¬∃ x : ℤ, 3*x≡2[ZMOD 7] ∧ 9*x≡12[ZMOD 15] ∧ 7*x≡1[ZMOD 31] ∧
    20*x≡4[ZMOD 30] ∧ 17*x≡14[ZMOD 21] ∧ 64*x≡83[ZMOD 105] ∧
    128*x≡833[ZMOD 1001] ∧ 987*x≡610[ZMOD 1597] ∧
    57*x≡87[ZMOD 105] ∧ 49*x≡5000[ZMOD 999] := by 
  rintro ⟨x, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩⟩
  norm_num [Int.ModEq] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  omega