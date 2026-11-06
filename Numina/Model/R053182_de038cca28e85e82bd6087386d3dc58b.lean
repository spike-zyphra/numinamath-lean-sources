import Mathlib

/- Given the positive divisors of a positive integer $n$ are arranged as: $1=d_1<d_2<d_3<\cdots $, then among $1$, $2$, $3$, $\cdots $, $2024$, the sum of all numbers for which $d_{10}=88$ is ___          ___. -/
theorem number_theory_8320 :
    ∑ n in (Finset.Icc 1 2024).filter (fun n => n.divisors.card ≥ 10 ∧ (n.divisors.sort LE.le)[9]! = 88), n = 2376 := by
  native_decide