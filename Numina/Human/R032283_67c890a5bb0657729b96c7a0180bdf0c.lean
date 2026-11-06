import Mathlib

/-
2. Let $A_{n}$ denote the product of multiples of $n$ not exceeding 100, where $n$ is a positive integer. For example, $A_{3}=3 \times 6 \times 9 \times \cdots \times 99$. Then the greatest common divisor of $A_{2}, A_{3}, A_{4}, \cdots, A_{17}$ is ( ).
(A)I
(B) 6
(C) 30
(D) 120
-/

def A (n : ℕ) := ∏ i ∈ Finset.Icc 1 100, if i % n = 0 then i else 1

theorem number_theory_328315 :
    IsGreatest {x | ∀ i ∈ Finset.Icc 2 17, x ∣ A i} 120 := by
  constructor
  · -- Show that 120 is in the set.
    intro i hi
    fin_cases hi <;> native_decide
  · -- Show there is no greater element in the set
    intro x hx
    have h1 : x ∣ A 17 := hx 17 (by norm_num)
    have h2 : A 17 ≠ 0 := by native_decide
    have h3 : x ∣ 120 := by
      have h17 : x ∣ A 17 := hx 17 (by norm_num)
      have h16 : x ∣ A 16 := hx 16 (by norm_num)
      have h15 : x ∣ A 15 := hx 15 (by norm_num)
      have h14 : x ∣ A 14 := hx 14 (by norm_num)
      have h13 : x ∣ A 13 := hx 13 (by norm_num)
      have h12 : x ∣ A 12 := hx 12 (by norm_num)
      have h11 : x ∣ A 11 := hx 11 (by norm_num)
      have h10 : x ∣ A 10 := hx 10 (by norm_num)
      have h9 : x ∣ A 9 := hx 9 (by norm_num)
      have h8 : x ∣ A 8 := hx 8 (by norm_num)
      have h7 : x ∣ A 7 := hx 7 (by norm_num)
      have h6 : x ∣ A 6 := hx 6 (by norm_num)
      have h5 : x ∣ A 5 := hx 5 (by norm_num)
      have h4 : x ∣ A 4 := hx 4 (by norm_num)
      have h3 : x ∣ A 3 := hx 3 (by norm_num)
      have h2 : x ∣ A 2 := hx 2 (by norm_num)
      exact Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd h2 h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17
    exact Nat.le_of_dvd (by norm_num) h3
