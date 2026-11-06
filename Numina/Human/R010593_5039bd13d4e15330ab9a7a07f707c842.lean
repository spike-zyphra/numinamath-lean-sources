import Mathlib

/- Nadir Airways offers three types of tickets for their flights from Boston to New York. The prices for the tickets are as follows: first-class tickets cost $70, second-class tickets cost $55, and stand-by tickets cost $39. On a particular flight, a total of 69 passengers purchased tickets, and the total revenue from these tickets was $3274. The task is to determine how many tickets of each type were sold.-/
theorem number_theory_4634 (h : numfirst + numsecond + numstandby = 69 ∧
    70 * numfirst + 55 * numsecond + 39 * numstandby = 3274) :
    numfirst=9 ∧numsecond=19 ∧ numstandby=41 := by
  omega
