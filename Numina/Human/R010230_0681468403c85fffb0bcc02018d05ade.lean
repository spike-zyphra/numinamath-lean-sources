import Mathlib

/- Is it possible to have 50 coins consisting only of pennies, dimes, and quarters that total $3?-/
theorem number_theory_4635 (h1 : p+d+q=50) (h2 : p+10*d+25*q=300) :
    False:= by
  omega
