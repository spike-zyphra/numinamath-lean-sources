import Mathlib

open BigOperators Real Set

theorem algebra_245421 {M N : Set ℝ}
  (hM : M = {x | ∃ m : ℤ, x = sin ((2*m-3)*π/6)}) (hN : N = {y | ∃ n : ℤ, y = cos (n*π/3)}) :
  M = N := by
  rw [hM, hN]
  apply Set.ext
  intro x
  constructor
  · -- Assume x ∈ M, show x ∈ N
    rintro ⟨m, hm⟩
    use 3 - m
    have eq : sin ((2 * m - 3) * π / 6) = cos ( (3 - m : ℤ) * π / 3 ) := by
      have h1 : sin ((2 * m - 3) * π / 6) = cos ((Real.pi / 2 - ((2 * m - 3) * Real.pi / 6)) ) := by
        have eq4 : sin ((2 * m - 3 : ℝ) * Real.pi / 6) = cos ((Real.pi / 2 : ℝ) - ((2 * m - 3 : ℝ) * Real.pi / 6)) := by
          rw [← cos_pi_div_two_sub]
        simpa using eq4
      have h2 : (Real.pi / 2 - ((2 * m - 3 : ℝ) * Real.pi / 6)) = ((3 - m : ℤ) * Real.pi / 3 : ℝ ) := by
        simp at *
        ring_nf 
      rw [h2] at h1
      exact h1
    rw [eq] at hm
    simpa using hm 
  · -- Assume x ∈ N, show x ∈ M
    rintro ⟨n, hn⟩
    use 3 - n 
    have eq : cos (n * π / 3 ) = sin ( (2 * (3 - n : ℤ) - 3) * π / 6 ) := by
      have h1 : cos (n * π / 3 ) = sin ( (Real.pi / 2 - (n * Real.pi / 3 )) ) := by 
        have eq4 : cos (n * Real.pi / 3 ) = sin ( (Real.pi / 2 : ℝ) - (n * Real.pi / 3 ) ) := by 
          rw [← sin_pi_div_two_sub]
        simpa using eq4 
      have h2 : (Real.pi / 2 - (n * Real.pi / 3 )) = ( (2 * ((3 - n : ℤ) : ℝ) - 3 ) * Real.pi / 6 : ℝ ) := by 
        simp at *
        ring_nf
      rw [h1, h2] 
    rw [eq] at hn
    simpa using hn