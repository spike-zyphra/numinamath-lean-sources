import Mathlib

/- A piggy bank contains 24 coins, which are all nickels, dimes, and quarters. The total value of these coins is two dollars. What combinations of nickels, dimes, and quarters can be found in the piggy bank?-/
theorem number_theory_4633 (n d q : ℕ) (h1 : n + d + q = 24)
    (h2 : 5*n+10*d+25*q=200) :
    (n=8∧d=16∧q=0) ∨ (n=11∧d=12∧q=1) ∨ (n=14∧d=8∧q=2) ∨
    (n=17∧d=4∧q=3) ∨ (n=20∧d=0∧q=4):= by
  omega
