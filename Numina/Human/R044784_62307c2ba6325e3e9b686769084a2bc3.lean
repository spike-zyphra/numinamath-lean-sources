import Mathlib

/- # Task 17-19. (2 points per Task)

Alena opened a multi-currency deposit at "Severny" Bank for 3 years.
The deposit involves the deposit of funds in three currencies: euros, dollars, and rubles.
At the beginning of the deposit agreement, Alena's account contained 3000 euros, 4000 dollars, and 240000 rubles.
The interest rate on the ruble deposit is 7.9% per annum, and on the dollar and euro deposits, it is 2.1% per annum.
Interest is accrued annually, and the interest is capitalized.
After one year, Alena decided to change the structure of her deposit, sold 1000 euros, and used the proceeds to increase the share of funds in dollars.
At the time of conversion
- the selling rate for dollars was 58.90 rubles
- the buying rate for dollars was 56.90 rubles
- the selling rate for euros was 61.15 rubles
- the buying rate for euros was 60.10 rubles.

Another year later, Alena reviewed the structure of her deposit again, exchanged 2000 dollars, and bought euros with the proceeds.
At the time of conversion
- the selling rate for dollars was 60.10 rubles
- the buying rate for dollars was 58.50 rubles
- the selling rate for euros was 63.20 rubles
- and the buying rate for euros was 61.20 rubles.

Question 17. Determine the balance on Alena's dollar account at the end of the deposit agreement (round to the nearest whole number).

Question 18. Determine the balance on Alena's euro account at the end of the deposit agreement (round to the nearest whole number).

Question 19. Determine the balance on Alena's ruble account at the end of the deposit agreement (round to the nearest whole number). -/
theorem algebra_281833 (e d r : ℕ → ℚ)
    (start : e 0 = 3000 ∧ d 0 = 4000 ∧ r 0 = 240000)
    (s1 : e 1 = e 0 * 1.021 ∧ d 1 = d 0 * 1.021 ∧ r 1 = 1.079 * r 0)
    (s2 : e 2 = (e 1 - 1000) * 1.021 ∧ d 2 = (d 1 + 1000 * 60.1 / 58.9) * 1.021 ∧ r 2 = 1.079 * r 1)
    (s3 : e 3 = (e 2 + 2000 * 58.5 / 63.2) * 1.021 ∧ d 3 = (d 2 - 2000) * 1.021 ∧ r 3 = 1.079 * r 2) :
    ⌊e 3⌋ = 4040 ∧ ⌊d 3⌋ = 3279 ∧ ⌊r 3⌋ = 301491 := by
    -- Substitute everything in and calculate
    constructor
    · rw [s3.left, s2.left, s1.left, start.left]
      norm_num
    · constructor
      · rw [s3.right.left, s2.right.left, s1.right.left, start.right.left]
        norm_num
      · rw [s3.right.right, s2.right.right, s1.right.right, start.right.right]
        norm_num