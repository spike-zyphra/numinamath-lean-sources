import Mathlib

/- At a clambake, the total cost of a lobster dinner is $11 and the cost of a chicken dinner is $8. Given the total bill amounts, what can we conclude about the possible combinations of lobster and chicken dinners if the total bill is:
a) $777 -/
theorem number_theory_4626_1 (x y : ℕ) (h : 11*x+8*y=777) :
    x=67 ∨x=59 ∨x=51 ∨x=43 ∨x=35 ∨x=27 ∨x=19 ∨x=11 ∨x=3 := by
  omega

/- At a clambake, the total cost of a lobster dinner is $11 and the cost of a chicken dinner is $8. Given the total bill amounts, what can we conclude about the possible combinations of lobster and chicken dinners if the total bill is:
a) $777 -/
theorem number_theory_4626_2 (x y : ℕ) (h : 11*x+8*y=777) :
    y=5 ∨y=16 ∨y=27 ∨y=38 ∨y=49 ∨y=60 ∨y=71 ∨y=82 ∨y=93 := by
  omega

/- At a clambake, the total cost of a lobster dinner is $11 and the cost of a chicken dinner is $8. Given the total bill amounts, what can we conclude about the possible combinations of lobster and chicken dinners if the total bill is:
b) $96 -/
theorem formal_3280_2_1 (x y : ℕ) (h : 11*x+8*y=96) :
    x=8 ∨x=0 := by
  omega

/- At a clambake, the total cost of a lobster dinner is $11 and the cost of a chicken dinner is $8. Given the total bill amounts, what can we conclude about the possible combinations of lobster and chicken dinners if the total bill is:
b) $96 -/
theorem formal_3280_2_2 (x y : ℕ) (h : 11*x+8*y=96) :
    y=1 ∨y=12 := by
  omega

/- At a clambake, the total cost of a lobster dinner is $11 and the cost of a chicken dinner is $8. Given the total bill amounts, what can we conclude about the possible combinations of lobster and chicken dinners if the total bill is:
c) $69 -/
theorem formal_3280_3 (x y : ℕ) (h : 11*x+8*y=69) :
    False:= by
  omega
