import Mathlib

/-
7.1. A natural number $n$ was multiplied by the sum of the digits of the number $3 n$, and the resulting number was then multiplied by 2. As a result, 2022 was obtained. Find $n$.
-/

theorem number_theory_233916 (n:ℕ):
n * (Nat.digits 10 (3*n)).sum  * 2 = 2022 ↔ n=337 := by 
  
  constructor
  
  --From left to right. We have that n is a divisor of 1011. Hence, we just need to check every case.
  intro h
  let y := (Nat.digits 10 (3 * n)).sum
  have eq : n * y = 1011 := by 
    simp [y]
    omega
  have nd1011 : n ∣ 1011 := by use y; omega
  have di1011 : Nat.divisors 1011 = {1, 3, 337, 1011} := by native_decide
  have : n ∈ Nat.divisors 1011 := by 
    rw [Nat.mem_divisors]
    simp [nd1011]
  simp [di1011] at this

  rcases this with ne | ne | ne | ne <;>
  simp [ne] at h 
  assumption


  --From right to left, simple calculation.
  intro ne
  simp [ne]