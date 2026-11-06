import Mathlib

open Finset
open Polynomial

/-Let $P_0(x) = x^3 + 313x^2 - 77x - 8\,$. For integers $n \ge 1\,$, define $P_n(x) = P_{n - 1}(x - n)\,$. What is the coefficient of $x\,$ in $P_{20}(x)\,$?-/
theorem algebra_20649 {P : ℕ → ℤ[X]} (hP0 : P 0 = X ^ 3 + 313 * X ^ 2 - 77 * X - 8)
    (hP : ∀ n ≥ 1, P n = (P (n - 1)).comp (X - (C n : ℤ[X]))) :
    (P 20).coeff 1 = 763 := by
  -- We have \[\begin{aligned} P_1(x) &= P_0(x-1), \\ P_2(x) &= P_1(x-2) = P_0(x-2-1), \\ P_3(x) &= P_2(x-3) = P_0(x-3-2-1), \end{aligned}\]and so on. We see that \[\begin{aligned} P_{20}(x) &= P_0(x-20-19-\dots-2-1) \\ &= P_0(x - 210), \end{aligned}\]using the formula $20 + 19 + \cdots + 2 + 1 = \tfrac{20(21)}{2} = 210.$ Thus, \[P_{20}(x) = (x-210)^3 + 313(x-210)^2 - 77(x-210) - 8.\]The coefficient of $x$ in this polynomial is \[\begin{aligned} 3 \cdot 210^2 - 313 \cdot 2 \cdot 210 - 77& = 210(3 \cdot 210 - 313 \cdot 2) - 77 \\ &= 210(630 - 626) - 77 \\ &= 210 \cdot 4 - 77 \\ &= \boxed{763}. \end{aligned}\]
  have : P 20 = (P 0).comp (X - (C 210 : ℤ[X])) := by
    rw [hP _ (by linarith)]; simp
    repeat first
      | simp; ring_nf
      | rw [hP _ (by linarith), Polynomial.comp_assoc]
  rw [this, hP0]
  simp
  ring_nf
  simp
  rw [show coeff (9261000 : ℤ[X]) 1 = 0 by apply coeff_ofNat_succ]
  rw [show coeff (44100 : ℤ[X]) 1 = 0 by apply coeff_ofNat_succ]
  norm_num
