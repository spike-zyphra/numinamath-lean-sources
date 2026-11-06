import Mathlib
open Finset Set Nat Real
set_option linter.unusedVariables false
noncomputable section

/-Let $C_2$ be a positive integer. Let $n, d$ be natural numbers.
The following conditions must hold:
(a) The base $n$ must be positive, $n > 0$.
(b) The digit $d$ must satisfy $0 \le d < n$.
(c) The digit $d$ must satisfy $d \le 9$.
(d) The digits $d, 2, C_2$ are used to represent a number in base $n$. Thus, $d < n$, $2 < n$, and $C_2 < n$.
(e) The digit $4$ is used to represent a number in base $n$. Thus, $4 < n$.
(f) The digit $d$ is used to represent a number in base $6$. Thus, $d < 6$.
Suppose that the number represented by the digits $[d, 2, C_2]$ in base $n$ (where $d$ is the least significant digit) is equal to $263$. This means $d + 2n + C_2 n^2 = 263$.
Suppose further that the number represented by the digits $[4, 2, C_2]$ in base $n$ (where $4$ is the least significant digit) is equal to the number represented by the digits $[1, d, 1, 1]$ in base $6$ (where $1$ is the least significant digit). This means $4 + 2n + C_2 n^2 = 1 \cdot 6^0 + d \cdot 6^1 + 1 \cdot 6^2 + 1 \cdot 6^3 = 253 + 6d$.
Show that these conditions and equations uniquely determine $C_2=3$, $d=2$, and $n=9$. Consequently, show that $n+d=11$.-/
theorem number_theory_637663 (C₂ d n : ℕ)
    (h_C₂_ge_1 : C₂ ≥ 1)
    (h_n_ge_5 : n ≥ 5)
    (h_d_le_5 : d ≤ 5)
    (h_d_lt_n : d < n)
    (h_C₂_lt_n : C₂ < n)
    (h_e1 : C₂ * n^2 + 2 * n + d = 263)
    (h_e2 : C₂ * n^2 + 2 * n + 4 = 253 + 6 * d)
    : C₂ = 3 ∧ d = 2 ∧ n = 9 := by
  -- Solve for $d$ from $h_e1$ and $h_e2$.
  have h_d_eq_2 : d = 2 := by
    have h_eq : 263 - d + 4 = 253 + 6 * d := by
      rw [← h_e1, ← h_e2]
      omega
    have h_d_eq : 7 * d = 14 := by
      linarith [h_eq]
    have h_d_div : d = 2 := by nlinarith
    exact h_d_div
  -- Substitute $d = 2$ into $h_e1$.
  have h_eq3 : C₂ * n^2 + 2 * n = 261 := by
    rw [h_d_eq_2] at h_e1
    linarith [h_e1]
  -- Solve for $n$ and $C₂$$.
  have h_n_eq_9 : n = 9 := by
    have h_n_div_261 : n ∣ 261 := by
      rw [← h_eq3]
      have : n ∣ C₂ * n ^ 2 := by
        rw [pow_two,← mul_assoc,mul_comm]
        exact Nat.dvd_mul_right n (C₂ * n)
      exact Nat.dvd_add this (Nat.dvd_mul_left n 2)
    -- Combine constraints $n ≥ 5$ and $$C₂ ≥ 1$ to bound $n$.
    have h_n_le_15 : n ≤ 15 := by
      have h_quadratic : n^2 + 2 * n ≤ 261 := by nlinarith
      have h_root : n ≤ 15 := by
        apply Nat.le_of_succ_le_succ
        suffices : 16 * 16 + 2 * 16 > 261
        · nlinarith
        norm_num
      exact h_root
    -- $261 = 3^2 * 29$, divisors are $1, 3, 9, 29, 87, 261$.
    have h_n_nine : n = 9 := by
      have h_divisors : n ∈ (261 :ℕ).divisors := by
        have : 261 ≠ 0 := by norm_num
        exact Nat.mem_divisors.mpr ⟨h_n_div_261,this⟩
      have h_divisors_261 : (261 : ℕ).divisors = {1, 3, 9, 29, 87, 261} := by decide
      have h_n : n = 1 ∨ n = 3 ∨ n = 9 ∨ n = 29 ∨ n = 87 ∨ n = 261 := by
        rw [h_divisors_261] at h_divisors
        simpa using h_divisors
      -- Since $n ≤ 15$, excludes $29$, $87$, $261$.
      have h_n' : n = 1 ∨ n = 3 ∨ n = 9 := by omega
      rcases h_n' with h1 | h3 | h9
      · linarith [h_n_ge_5]
      · linarith [h_n_ge_5]
      · exact h9
    exact h_n_nine
  -- Substitute $n = 9$ into $h_eq3$ to solve for $C₂$.
  have h_C₂_eq_3 : C₂ = 3 := by
    rw [h_n_eq_9] at h_eq3
    have h_C₂_calc : C₂ * 81 = 243 := by
      linarith [h_eq3]
    have h_C₂_div : C₂ = 3 := by nlinarith
    exact h_C₂_div
  -- Combine results.
  have h_solution : C₂ = 3 ∧ d = 2 ∧ n = 9 := by
    exact ⟨h_C₂_eq_3, h_d_eq_2, h_n_eq_9⟩
  -- show $n + d$ equal $11$.
  have h_target: n + d = 11 := by linarith
  exact h_solution
