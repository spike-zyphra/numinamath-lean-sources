import Mathlib

/- The manager of a company planned to distribute a 50$ bonus to each employee from the company fund,
but the fund contained 5$ less than what was needed. 
Instead the manager gave each employee a 45$ bonus and kept the remaining 95$ in the company fund.  
The amount of money in the company fund before any bonuses were paid was
(A) 945 dollars(B) 950 dollars(C) 955 dollars(D) 990 dollars(E) 995 dollars -/

theorem algebra_93383 {n : ℕ} (hn : n > 0) (h : 50 * n - 5 = 45 * n + 95) :
50 * n - 5 = 995 := by omega
--LHS and RHS of h are both equal to the money in the fund. The claim amounts to solving the equation.