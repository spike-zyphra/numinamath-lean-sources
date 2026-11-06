import Mathlib

/-
Let $M$ be a positive integer. Compute the sum $S = \sum_{i=0}^{M-1} \frac{15(10^i-1)}{9}$.
Show that the answer is $\frac{5}{27}(10(10^{M-1}-1)-9(M-1))$.
-/

theorem number_theory_636980 (M : ℕ) (Mpos : 0 < M) :
  ∑ i ∈ Finset.range M, ((15:ℝ) * (10 ^ i - 1) / 9) = (5:ℝ) / 27 * (10 * (10 ^ (M-1) - 1) - 9 * (M - 1)) := by

  --We prove this by a simple induction on M.
  induction' M with M hM

  simp at Mpos

  by_cases Me0 : M = 0 
  simp [Me0]
  have Mpos : 0 < M := by omega
  simp [Mpos] at hM
  simp
  rw [Finset.sum_range_succ]
  rw [hM]
  ring_nf
  field_simp

  have : (10:ℝ) ^ M = 10 ^ (M-1) * 10 := by 
    have : M = M - 1 + 1 := by omega
    nth_rw 1 [this]
    rw [pow_succ]
  rw [this]
  ring
