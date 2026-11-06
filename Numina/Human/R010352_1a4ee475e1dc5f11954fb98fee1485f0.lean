import Mathlib

/-Rodney uses the following clues to try to guess a secret number:
\begin{tabular}{ c }
It is a two-digit integer.\
The tens digit is odd.\
The units digit is even.\
The number is greater than 65.
\end{tabular}If Rodney guesses a number that has each of these properties, what is the probability that Rodney will guess the correct number? Express your answer as a common fraction.-/
theorem algebra_17179 :
    {n | n ∈ Finset.Icc 66 99 ∧ Odd (n / 10) ∧ Even (n % 10)}.ncard = 10 := by
  simp

  -- We need to count the number of two-digit integers with odd tens digit and even units digit that are greater than $65.$ Notice that the only two possibilities for the tens digit are $7$ and $9.$ For each of these, the units digits $0,$ $2,$ $4,$ $6,$ and $8$ are all possible, for a total of $5$ choices. Therefore there are $2\cdot 5=10$ possible integers to choose from. Since there are $10$ integers to choose from, the probability of selecting the right one is $\boxed{\frac{1}{10}}.$
  -- For your information, the possible numbers are $$\{ 70, 72, 74, 76, 78, 90, 92, 94, 96, 98 \}.$$

  have : {n | (66 ≤ n ∧ n ≤ 99) ∧ Odd (n / 10) ∧ Even (n % 10)} = {
      70,72,74,76,78,90,92,94,96,98
  } := by
    ext n
    simp
    constructor
    . simp
      intro hn₁ hn₂ hn₃ hn₄
      have hn₄: n % 2 = 0 := by
        rw [Nat.even_iff] at hn₄
        omega
      have hn₃: (n / 10) % 2 = 1 := by
        rw [Nat.odd_iff] at hn₃
        exact hn₃
      omega
    . intro hn
      use (by omega)
      constructor
      . apply Nat.odd_iff.mpr
        omega
      apply Even.mod_even
      exact Nat.even_iff.mpr (by omega)
      exact Nat.even_iff.mpr (rfl)
  rw [this]
  repeat rw [Set.insert_eq, Set.ncard_union_eq, Set.ncard_singleton]
  rw [Set.ncard_singleton]
  repeat simp
