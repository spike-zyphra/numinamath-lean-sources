import Mathlib

/-
Let $N$ be a positive integer. Show that the sum $\sum_{i=0}^{N-1} \left(\frac{10^i-1}{9}+1\right)$ is equal to $\frac{10^N-1+72N}{81}$.
-/

theorem number_theory_639468 (N:ℕ) (Npos: 0 < N):
  ∑ i ∈ Finset.range N, ((10 ^ (i) - (1:ℝ))/(9:ℝ) + 1) = (10 ^ N - 1 + 72 * N)/(81:ℝ) := by

  --We prove it by induction.
  induction' N with N hN
  
  --The base case is trivial.
  simp at Npos ⊢

  by_cases Ne0: N = 0
  simp [Ne0]
  norm_num
  have Npos : 0 < N := by omega
  simp [Npos] at hN
  simp

  --Just use the induction hypothesis.
  rw [Finset.sum_range_succ]
  rw [hN]
  field_simp
  ring
  


