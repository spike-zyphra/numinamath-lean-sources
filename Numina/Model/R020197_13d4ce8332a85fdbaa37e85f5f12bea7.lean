import Mathlib

theorem number_theory_171212 (n : ℤ) (h : (n^2) / 10 % 10 = 7) :
    (n^2) % 10 = 6 := by
  have h1 : n^2 % 100 = 70 + (n ^ 2 % 10) := by
    omega
  have h2 : n^2 % 4 = 0 ∨ n^2 % 4 = 1 := by
    have h1 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1]
  have h4 : n^2 % 25 = 0 ∨ n^2 % 25 = 1 ∨ n^2 % 25 = 4 ∨ n^2 % 25 = 6 ∨ n^2 % 25 = 9 ∨ n^2 % 25 = 11 ∨ n^2 % 25 = 14 ∨ n^2 % 25 = 16 ∨ n^2 % 25 = 19 ∨ n^2 % 25 = 21 ∨ n^2 % 25 = 24 := by
    have h1 : n % 25 = 0 ∨ n % 25 = 1 ∨ n % 25 = 2 ∨ n % 25 = 3 ∨ n % 25 = 4 ∨ n % 25 = 5 ∨ n % 25 = 6 ∨ n % 25 = 7 ∨ n % 25 = 8 ∨ n % 25 = 9 ∨ n % 25 = 10 ∨ n % 25 = 11 ∨ n % 25 = 12 ∨ n % 25 = 13 ∨ n % 25 = 14 ∨ n % 25 = 15 ∨ n % 25 = 16 ∨ n % 25 = 17 ∨ n % 25 = 18 ∨ n % 25 = 19 ∨ n % 25 = 20 ∨ n % 25 = 21 ∨ n % 25 = 22 ∨ n % 25 = 23 ∨ n % 25 = 24 := by
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1]
  have h3 : n^2 % 4 = (70 + (n^2 % 10)) % 4 := by
    omega
  have h5 : n^2 % 25 = (70 + (n^2 % 10)) % 25 := by
    omega
  omega