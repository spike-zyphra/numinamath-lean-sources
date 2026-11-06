import Mathlib

def doubleFactorial (n : ℕ) : ℕ := if Odd n then ∏ i ∈ Finset.range ((n + 1) / 2), (n - 2 * i) else ∏ i ∈ Finset.range (n / 2), (n - 2 * i)

theorem number_theory_65818 : 1987 ∣ doubleFactorial 1986 + doubleFactorial 1985 := by 
  native_decide