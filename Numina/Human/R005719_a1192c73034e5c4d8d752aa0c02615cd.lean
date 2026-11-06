import Mathlib

/-
Evaluate $\frac{2016!^{2}}{2015!2017!}$. Here $n$ ! denotes $1 \times 2 \times \cdots \times n$.
-/

theorem combinatorics_609586 : 
(Nat.factorial 2016)^2 / (Nat.factorial 2015 * Nat.factorial 2017) = (2016:ℝ) / (2017:ℝ) := by
  have : Nat.factorial (2016+1) = (2016+1) * Nat.factorial 2016 := by apply Nat.factorial_succ
  simp at this
  rw [this]
  field_simp  
  rw [pow_two]
  have : Nat.factorial (2015+1) = (2015+1) * Nat.factorial 2015 := by apply Nat.factorial_succ
  simp at this
  nth_rw 1 [this]
  field_simp
  ring_nf
