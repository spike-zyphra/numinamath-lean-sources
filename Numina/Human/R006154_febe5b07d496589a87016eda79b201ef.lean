import Mathlib
/- Using the digits $1$, $9$, $9$, $0$, form all possible four-digit numbers. For each such four-digit number, when added to a natural number $n$, the sum is not congruent to $1$ modulo $7$. List all natural numbers $n$ that satisfy the above condition in ascending order: ${{n}_{1}}<{}{{n}_{2}}<{}{{n}_{3}}<{}{{n}_{4}}<{}\cdots$. Find the value of ${{n}_{1}}\cdot {{n}_{2}}$.-/
theorem number_theory_2351 : ∃ n1 n2, n1 < n2 ∧ ¬(n1 + 1999 ≡ 1 [MOD 7]) ∧ ¬(n2 + 1999 ≡ 1 [MOD 7]) ∧ n1 * n2 = 28 := by
  use 2, 14
  refine ⟨by norm_num, by norm_num [Nat.ModEq], by norm_num [Nat.ModEq], by norm_num⟩
