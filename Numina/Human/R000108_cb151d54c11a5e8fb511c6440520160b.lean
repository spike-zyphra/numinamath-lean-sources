import Mathlib

/- A postal clerk has only 14-cent and 21-cent stamps to sell. What combinations of these stamps can be used to mail a package requiring postage of exactly:
a) $3.50 -/
theorem number_theory_4625_1_1 (x y : ℕ) (h : 14*x+21*y=350) :
    x=1 ∨ x=4 ∨ x=7 ∨ x=10 ∨ x=13 ∨x=16 ∨ x=19  ∨ x=22 ∨ x=25 := by
  omega

/- A postal clerk has only 14-cent and 21-cent stamps to sell. What combinations of these stamps can be used to mail a package requiring postage of exactly:
a) $3.50 -/
theorem number_theory_4625_1_2 (x y : ℕ) (h : 14*x+21*y=350) :
    y=0 ∨y=2 ∨y=4 ∨y=6 ∨y=8 ∨y=10 ∨y=12 ∨y=14 ∨y=16 := by
  omega

/- A postal clerk has only 14-cent and 21-cent stamps to sell. What combinations of these stamps can be used to mail a package requiring postage of exactly:
b) $4.00-/
theorem number_theory_4625_2 (x y : ℕ) (h : 14*x+21*y=400) :
    False := by
  omega

/- A postal clerk has only 14-cent and 21-cent stamps to sell. What combinations of these stamps can be used to mail a package requiring postage of exactly:
b) $4.00 -/
theorem number_theory_4625_3_1 (x y : ℕ) (h : 14*x+21*y=777) :
    x=54 ∨x=51 ∨x=48 ∨x=45 ∨x=42 ∨x=39 ∨x=36 ∨x=33 ∨x=30 ∨x=27 ∨
    x=24 ∨x=21 ∨x=18 ∨x=15 ∨x=12 ∨x=9 ∨x=6 ∨x=3 ∨x=0 := by
  omega

/- A postal clerk has only 14-cent and 21-cent stamps to sell. What combinations of these stamps can be used to mail a package requiring postage of exactly:
c) $7.77?-/
theorem number_theory_4625_3_2 (x y : ℕ) (h : 14*x+21*y=777) :
    y=1 ∨y=3 ∨y=5 ∨y=7 ∨y=9 ∨y=11 ∨y=13 ∨y=15 ∨y=17 ∨y=19 ∨y=21 ∨
    y=23 ∨y=25 ∨y=27 ∨y=29 ∨y=31 ∨y=33 ∨y=35 ∨y=37 := by
  omega
