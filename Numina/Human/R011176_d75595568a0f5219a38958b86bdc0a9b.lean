import Mathlib

/-A positive integer $n$ is called "flippant" if $n$ does not end in 0 (when written in decimal notation) and, moreover, $n$ and the number obtained by reversing the digits of $n$ are both divisible by 7 . How many flippant integers are there between 10 and 1000 ?-/

theorem number_theory_611460 :
    {n ∈ Finset.Icc 10 1000 | ¬10 ∣ n ∧ 7 ∣ n ∧ 7 ∣ Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))}.card = 17 := by
    native_decide