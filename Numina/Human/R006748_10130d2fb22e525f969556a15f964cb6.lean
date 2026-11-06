import Mathlib

/- A mathematician is asked about their license plate number. They reply: "It's a four-digit number, of which the last three digits are the same. Let the first digit be $a$ and the common digit for the last three positions be $b$. The sum of its four digits is 18. If you place the first digit $a$ at the end of the number, the resulting four-digit number is 1998 less than the actual license plate number."
Determine the license plate number. Show the answer is 6444. -/
theorem number_theory_640756
  (a b : ℕ)
  (ha : 0 ≤ a ∧ a ≤ 9)
  (hb : 0 ≤ b ∧ b ≤ 9)
  (H1 : a + b + b + b = 18)
  (H2 : 1000 * b + 100 * b + 10 * b + a = 1000 * a + 100 * b + 10 * b + b - 1998)
  : 1000 * a + 100 * b + 10 * b + b = 6444 :=
by
  omega
