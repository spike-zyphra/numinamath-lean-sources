import Mathlib

/-- Define sol as the set of positive integers less than 2019 that are 20-pretty. -/
def sol_4096 := (List.range 2019).filter fun a => (Nat.divisors a).card = 20 ∧ 20 ∣ a

/-- positive integers less than 2019 that are 20-pretty are  [240, 560, 880, 1040, 1360, 1520, 1840, 2000] -/
lemma aux_4096 : sol_4096 = [240, 560, 880, 1040, 1360, 1520, 1840, 2000] := by native_decide

def solution_4096 := [240, 560, 880, 1040, 1360, 1520, 1840, 2000]

/-- Call a positive integer $n$ $k$-pretty if $n$ has exactly $k$ positive divisors and $n$ is divisible by $k$. For example, $18$ is $6$-pretty. Let $S$ be the sum of positive integers less than $2019$ that are $20$-pretty. Find $\tfrac{S}{20}$.
-/
theorem number_theory_4096 : solution_4096.sum / 20 = 472 := by decide
