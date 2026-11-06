import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_274153 {z : ℂ} (hz : z = I) :
    IsLeast {n | 0 < n ∧ z ^ n = 1} 4 := by 
  rw [hz]
  constructor
  · -- Show 4 is in the set
    constructor
    · norm_num
    · -- Show that I^4 = 1
      have h1 : I ^ 4 = 1 := by
        calc
          I ^ 4 = (I ^ 2) ^ 2 := by ring
          _ = (-1) ^ 2 := by simp [Complex.I_sq]
          _ = 1 := by norm_num
      simpa using h1
  · -- We need to prove that for all n in the set, 4 ≤ n
    intro n hn
    have ⟨hn_pos, hn_pow⟩ := hn
    by_contra h
    push_neg at h
    have h2 : n < 4 := by omega
    interval_cases n <;> norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I] at hn_pow <;> norm_num at hn_pow <;> try contradiction