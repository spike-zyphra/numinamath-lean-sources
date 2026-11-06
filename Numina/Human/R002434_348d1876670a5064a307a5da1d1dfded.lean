import Mathlib
open Mathlib

/-- There is a positive integer $n$ such that $(n+1)! + (n+2)! = n! \cdot 440$. What is the sum of the digits of $n$?

$\textbf{(A) }3\qquad\textbf{(B) }8\qquad\textbf{(C) }10\qquad\textbf{(D) }11\qquad\textbf{(E) }12$ -/
theorem algebra_93340 {n : ℕ} (hn : n > 0) (h : Nat.factorial (n + 1) + Nat.factorial (n + 2) = Nat.factorial n * 440) :
(Nat.digits 10 n).sum = 10 := by
  -- https://artofproblemsolving.com/wiki/index.php/2019_AMC_10B_Problems/Problem_6

  -- divide both sides by n!
  have uncom : (Nat.factorial (n + 1) + Nat.factorial (n + 2)) / Nat.factorial n = (Nat.factorial n * 440) / Nat.factorial n := by rw [h]
  have da := Nat.factorial_ne_zero n
  have ca : n.factorial > 0 := by omega
  rw [Nat.add_div ca] at uncom
  simp only [Nat.factorial, Nat.succ_eq_add_one, Nat.mul_mod_left, zero_add] at uncom
  simp only [←Nat.mul_assoc] at uncom
  simp only [Nat.mul_div_cancel _ ca, Nat.mul_mod_left, nonpos_iff_eq_zero, da, ↓reduceIte,
    add_zero, Nat.mul_div_cancel_left _ ca] at uncom
  
  -- we have n^2 + 4n - 437 = 0
  have kw : ((↑n : ℤ) - 19) * ((↑n : ℤ) + 23) = 0 := by
    zify at *
    ring_nf at uncom
    ring_nf
    linarith
  rw [mul_eq_zero] at kw
  obtain kw | kw := kw
  -- if n = 19, the goal is true
  · rw [(by zify; linarith : n = 19)]
    simp only [Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos, Nat.reduceMod,
      Nat.reduceDiv, Nat.lt_one_iff, pos_of_gt, Nat.one_mod, Nat.digits_zero, List.sum_cons,
      List.sum_nil, add_zero, Nat.reduceAdd]
  -- n can't be -23
  · have js : 0 ≤ (↑n : ℤ) := by aesop
    linarith