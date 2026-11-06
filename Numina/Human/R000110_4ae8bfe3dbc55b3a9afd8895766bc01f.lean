import Mathlib

/- Which combinations of pennies, dimes, and quarters can be used to make a total value of 99 cents?-/
theorem  number_theory_4630_1 (x y z : ℕ) (h : 1*x+10*y+25*z=99) :
    x=64∨x=34∨x=99∨x=4∨x=69∨x=39∨x=9∨x=74∨x=44∨x=14∨x=79∨x=49∨
    x=19∨x=54∨x=24∨x=89∨x=59∨x=29:= by
  omega

/- Which combinations of pennies, dimes, and quarters can be used to make a total value of 99 cents?-/
theorem  number_theory_4630_2 (x y z : ℕ) (h : 1*x+10*y+25*z=99) :
    y=0∨y=1∨y=2∨y=3∨y=4∨y=5∨y=6∨y=7∨y=8∨y=9:= by
  omega

/- Which combinations of pennies, dimes, and quarters can be used to make a total value of 99 cents?-/
theorem  number_theory_4630_3 (x y z : ℕ) (h : 1*x+10*y+25*z=99) :
    z=0∨z=1∨z=2∨z=3:= by
  omega
