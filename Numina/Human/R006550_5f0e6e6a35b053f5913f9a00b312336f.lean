import Mathlib

/-
Let $M$ be a positive integer. Prove the identity that the sum of the cubes of the first $M$ positive integers is equal to the square of the sum of the first $M$ positive integers. That is, show that $\sum_{k=1}^{M} k^3 = \left(\sum_{k=1}^{M} k\right)^2$.
-/

theorem number_theory_638427 (M : ℕ) (Mpos : 0 < M):
  ∑ i in Finset.Icc 1 M, i ^ 3 = (∑ i in Finset.Icc 1 M, i) ^ 2 := by

  --The sum of first n integers.
  have b : ∀ N : ℕ, ∑ i in Finset.Icc 1 (N+1), (i:ℝ) = (N+1)*(N+2)/2 := by  
    intro N
    induction' N with N hN

    simp

    rw [Finset.sum_Icc_succ_top]
    rw [hN]
    ring_nf
    field_simp
    ring
    linarith

  --Now, our claim follows from a simple induction.
  have cla : ∀ N : ℕ, ∑ i in Finset.Icc 1 (N+1), i ^ 3 = (∑ i in Finset.Icc 1 (N+1), i) ^ 2 := by 
    rify

    intro N
    induction' N with N hN

    simp

    rw [Finset.sum_Icc_succ_top]
    nth_rw 2 [Finset.sum_Icc_succ_top]
    have : ∑ k ∈ Finset.Icc 1 (N + 1), (k:ℝ) = (N+1)*(N+2)/2 := by apply b
    rw [hN,this]
    ring_nf
    field_simp
    ring
    linarith
    linarith

  have exi : ∃ N : ℕ, N + 1 = M := by use M - 1; omega
  obtain ⟨N,hN⟩ := exi
  specialize cla N
  rw [hN] at cla
  exact cla