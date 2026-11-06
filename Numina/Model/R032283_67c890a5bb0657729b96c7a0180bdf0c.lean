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
  · -- Show 120 is in the set
    intro i hi
    have h1 : i ≥ 2 := by
      have h2 : i ∈ Finset.Icc (2 : ℕ) (17 : ℕ) := by simpa using hi
      simp at h2 ⊢
      omega
    have h2 : i ≤ 17 := by
      have h3 : i ∈ Finset.Icc (2 : ℕ) (17 : ℕ) := by simpa using hi
      simp at h3 ⊢
      omega
    interval_cases i <;> native_decide
  · -- Show that 120 is greatest
    intro x hx
    have h1 : ∀ i ∈ Finset.Icc 2 17, x ∣ A i := hx
    have h2 : x ∣ A 2 := h1 2 (by norm_num)
    have h3 : x ∣ A 3 := h1 3 (by norm_num)
    have h4 : x ∣ A 4 := h1 4 (by norm_num)
    have h5 : x ∣ A 5 := h1 5 (by norm_num)
    have h6 : x ∣ A 6 := h1 6 (by norm_num)
    have h7 : x ∣ A 7 := h1 7 (by norm_num)
    have h8 : x ∣ A 8 := h1 8 (by norm_num)
    have h9 : x ∣ A 9 := h1 9 (by norm_num)
    have h10 : x ∣ A 10 := h1 10 (by norm_num)
    have h11 : x ∣ A 11 := h1 11 (by norm_num)
    have h12 : x ∣ A 12 := h1 12 (by norm_num)
    have h13 : x ∣ A 13 := h1 13 (by norm_num)
    have h14 : x ∣ A 14 := h1 14 (by norm_num)
    have h15 : x ∣ A 15 := h1 15 (by norm_num)
    have h16 : x ∣ A 16 := h1 16 (by norm_num)
    have h17 : x ∣ A 17 := h1 17 (by norm_num)
    have h18 : x ∣ 120 := by
      exact Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd h2 h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17
    have h19 : x ≤ 120 := by
      exact Nat.le_of_dvd (by norm_num) h18
    linarith