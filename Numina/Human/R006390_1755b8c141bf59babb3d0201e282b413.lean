import Mathlib

open Finset

-- define the solution N_L
def N_L
  |2 => 36
  |3 => 108
  |4 => 216
  |5 => 216
  |_ => 0

/--Let L be an integer such that 2≤L≤5. A student ID number has L digits
d1d2...dL.Each digit di must be an integer from 1 to 9 (inclusive).
The ID number must satisfy the following properties: For each integer k from 2 to L,
the number formed by the first k digits (e.g., d1d2...dk, interpreted as a base 10 number) is divisible by k.
Determine the number of such L-digit student ID numbers. Show that this number is
N_L=9*4*..*c_L, where cL is the number of choices for the k-th digit dk  given the previous digits, specifically
c3=3, c4=2, and c5 = 1 (The product c3=3, c4=2, and c5=1)​
is taken to be 1 if L=2). The number of such IDs are:
.-/

theorem number_theory_636584 (L: ℕ) (h1: 2 ≤ L) (h2: L ≤ 5):

  ((Ico (10 ^ (L - 1)) (10 ^ L)).filter
  (fun n => n % 10 ≠ 0 ∧ 2 ∣ n / 10 ^ (L - 2) ∧
  (L < 3 ∨ (3 ∣ n / 10 ^ (L - 3) ∧ (n / 10) % 10 ≠ 0)) ∧
  (L < 4 ∨ (4 ∣ n / 10 ^ (L - 4) ∧ (n / 100) % 10 ≠ 0)) ∧
  (L < 5 ∨ (5 ∣ n / 10 ^ (L - 5) ∧ (n / 1000) % 10 ≠ 0)))).card = N_L L := by

  -- when formalizing, we need to ensure two things: k ∣ d1d2..dk and any di is nonzero
  simp [N_L]
  interval_cases L
  all_goals native_decide
