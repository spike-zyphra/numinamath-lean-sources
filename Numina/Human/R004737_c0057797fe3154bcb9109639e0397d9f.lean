import Mathlib

open Real

/-13. Define the recursive sequence $\left\{F_{n}\right\}$ :
$$
F_{0}=0, F_{1}=1 \text {, }
$$
$F_{n}(n \geqslant 2)$ is the remainder of $F_{n-1}+F_{n-2}$ divided by 3, i.e., the sequence $\left\{F_{n}\right\}: 0,1,1,2,0,2,2,1,0, \cdots$.
Then the value of $\sum_{i=2017}^{2024} F_{i}$ is ( ).
(A) 6
(B) 7
(C) 8
(D) 9
(E) 10-/
theorem number_theory_312941 {F : ℕ→ℕ} (hF₀ : F 0 = 0) (hF₁ : F 1 = 1) (hF₂ : ∀n ≥ 2, F n = (F (n - 1) + F (n - 2)) % 3) : ∑ i ∈ Finset.Icc 2017 2024, F i = 9 := by
  -- First, we will show that F_n = Nat.fib n % 3 for all n
  have hF : ∀ n, F n = Nat.fib n % 3 := by
    intro n
    induction' n using Nat.strongRec with n ih
    by_cases hn₁ : n < 2
    · obtain (hn | hn) := show n = 0 ∨ n = 1 by omega
      all_goals {
        rw [hn]
        norm_num
        assumption
      }
    push_neg at hn₁
    specialize hF₂ n hn₁
    have hfib : Nat.fib n = Nat.fib (n - 1) + Nat.fib (n - 2) := by
      rw [show n = (n - 2) + 2 by omega, Nat.fib_add_two]
      norm_num
      linarith
    rw [hfib, hF₂, ih, ih]
    all_goals omega
  suffices ∑ i ∈ Finset.Icc 2017 2024, F i = ∑ i ∈ Finset.Icc 2017 2024, (Nat.fib i % 3) by
    rw [this]
    native_decide
  apply Finset.sum_congr rfl
  exact fun x a ↦ hF x
