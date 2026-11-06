import Mathlib

open Polynomial

theorem algebra_170174 {roots : Multiset ℂ}
    (hr₁ : roots = (X^3 - C 13 * X ^ 2 + C 24 * X - C 22 : ℂ[X]).roots)
    (hr₂ : 1 + Complex.I ∈ roots) :
    {x : ℝ | (x : ℂ) ∈ roots} = {11} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, prove that if x ∈ {x : ℝ | (x : ℂ) ∈ roots}, then x = 11
    intro h
    have h3 : (x : ℂ) ∈ roots := by 
      simpa using h 
    rw [hr₁] at h3
    have h4 : ((X^3 - C 13 * X ^ 2 + C 24 * X - C 22 : ℂ[X]) : ℂ[X]).eval (x : ℂ) = 0 := by 
      simp at h3 ⊢
      <;> try { 
        tauto 
      }
      all_goals norm_num at h3 ⊢ 
      all_goals try tauto 
    have eq1 : (x : ℂ) ^ 3 - 13 * (x : ℂ) ^ 2 + 24 * (x : ℂ) - 22 = 0 := by 
      simpa using h4 
    have eq2 : (x : ℝ) ^ 3 - 13 * (x : ℝ) ^ 2 + 24 * (x : ℝ) - 22 = 0 := by 
      norm_num [pow_two, pow_succ, Complex.ext_iff] at eq1 ⊢ 
      all_goals ring_nf at eq1 ⊢ 
      all_goals linarith 
    have h5 : (x - 11) * ((x : ℝ) ^ 2 - 2 * (x : ℝ) + 2) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- Case h6 : x - 11 = 0, so x = 11 
      linarith 
    · -- Case h7: x ^ 2 - 2 * x + 2 = 0 
      have h8 : (x : ℝ) ^ 2 - 2 * (x : ℝ) + 2 = 0 := by
        linarith 
      have h9 : (x - 1) ^ 2 ≥ 0 := by 
        apply sq_nonneg 
      nlinarith 
  · -- Now prove the reverse. If x = 11, then x ∈ {x : ℝ | (x : ℂ) ∈ roots}
    intro h 
    rw [h]
    have h11_in : (11 : ℂ) ∈ roots := by
      rw [hr₁] 
      have h5 : ((X^3 - C 13 * X ^ 2 + C 24 * X - C 22 : ℂ[X]) : ℂ[X]).eval (11 : ℂ) = 0 := by 
        simp [pow_two, pow_succ]
        <;> norm_num [Complex.ext_iff] 
      have h55 : (11 : ℂ) ∈ ((X^3 - C 13 * X ^ 2 + C 24 * X - C 22 : ℂ[X]).roots) := by 
        simp_all [mem_roots, h5] 
      simpa using h55 
    simp [h11_in]