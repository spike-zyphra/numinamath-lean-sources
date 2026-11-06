import Mathlib

open Real Set
open scoped Real

theorem Other_24511 (n : ℕ) (npos : n > 0) (x : ℝ) : (cos x) ^ n - (sin x) ^ n = 1 ↔
    (Even n ∧ (∃ m : ℤ, x = m * π) ∨ (Odd n ∧ ((∃ m : ℤ, x = -π / 2 + m * (2 * π)) ∨ (∃ m : ℤ, x = m * (2 * π))))) := by
  constructor
  intro h
  have : Even n ∨ Odd n := by exact Nat.even_or_odd n
  rcases this with evenn | oddn
  
  --The case where n is even.
  --Then sin x ^n ≥ 0, so cos x = 1 or -1 and sin x = 0.
  left
  simp [evenn]
  have cosxabseq : cos x = 1 ∨ cos x = -1 := by
    have : cos x ^ n = 1 := by 
      have ucos : cos x ^ n ≤ 1 := by 
        obtain ⟨k,hk⟩ := evenn
        rw [hk]
        have : k + k = 2*k := by ring
        rw [this,pow_mul]
        rw [pow_le_one_iff_of_nonneg]
        simp
        exact abs_cos_le_one x
        exact sq_nonneg (cos x)
        by_contra ke0
        simp [ke0] at hk
        simp [hk] at npos
      have lsin : 0 ≤ sin x ^ n := by exact Even.pow_nonneg evenn (sin x)
      linarith
    have : cos x ^ 2 = 1 := by 
      obtain ⟨k,hk⟩ := evenn
      rw [hk] at this
      have t1: k + k = 2*k := by ring
      rw [t1] at this
      rw [pow_mul] at this
      rw [pow_eq_one_iff_cases] at this
      have kne0: ¬ k = 0 := by 
        by_contra ke0
        simp [ke0] at hk
        simp [hk] at npos
      have cosx2nneg: 0 ≤ cos x ^2 := by exact sq_nonneg (cos x)
      rcases this with this | this | this
      contradiction
      exact this
      linarith
    simp at this
    exact this
  rcases cosxabseq with coseq1 | coseqm1
  rw [cos_eq_one_iff] at coseq1
  obtain ⟨k,hk⟩ := coseq1
  use 2 * k
  rw [← hk]
  have : @Int.cast ℝ instIntCast (2 * k) = (2*k) := by norm_cast
  rw [this]
  ring
  rw [cos_eq_neg_one_iff] at coseqm1
  obtain ⟨k,hk⟩ := coseqm1
  use (2*k+1)
  rw [← hk]
  have : @Int.cast ℝ instIntCast (2 * k + 1) = 2*k+1 := by norm_cast
  rw [this]
  ring

  --The case where n is odd.
  right
  simp [oddn]
  
  --We divide it into two cases : n = 1 or n ≥ 3.
  
  --The case n = 1 can be calculated directly.
  by_cases ne1 : n = 1
  simp [ne1] at h
  have eq : cos (π/4) = cos (x + π/4) := by 
    simp [cos_add]
    have : cos x * (√2 / 2) - sin x * (√2 / 2) = (cos x - sin x) * (√2 / 2) := by ring
    rw [this]
    rw [h]
    ring
  rw [Real.cos_eq_cos_iff] at eq
  obtain ⟨k, eq⟩ := eq
  rcases eq with eq | eq
  right
  use k
  field_simp at eq
  rw [eq]
  ring
  left
  use k
  linarith

  --When 3 ≤ n, since cos x ^2 + sin x ^2 = 1. We must have that sin x = 0 or -1.
  have nge3 : 3 ≤ n := by 
    obtain ⟨k,hk⟩ := oddn
    have : 0 < k := by 
      by_contra kk
      have ke0 : k = 0 := by omega
      simp [ke0] at hk
      contradiction
    linarith only [this,hk]
  
  by_cases sinpos : 0 < sin x
  have : 0 < sin x ^ n := by exact pow_pos sinpos n
  have t1: 1 < cos x ^ n := by linarith only [h,this]
  have : cos x ≤ 1 := by exact cos_le_one x
  have : 0 ≤ cos x := by 
    by_contra cosneg
    push_neg at cosneg
    have cosxnneg: cos x ^ n < 0 := by exact Odd.pow_neg oddn cosneg
    linarith only [cosxnneg, t1]
  have t2: cos x ^ n ≤ 1 := by 
    apply pow_le_one₀
    exact this
    assumption
    
  linarith only [t1,t2]
  by_cases sine0 : sin x = 0
  simp [sine0] at h
  field_simp at h
  have cose1 : cos x = 1 := by 
    rw [pow_eq_one_iff_cases] at h
    rcases h with h|h|h
    linarith only [npos,h]
    exact h
    have : ¬ Even n := by exact Nat.not_even_iff_odd.mpr oddn
    have _ := h.right
    contradiction
  rw [cos_eq_one_iff] at cose1
  right
  obtain ⟨k,hk⟩ := cose1
  use k
  symm; exact hk
  by_cases sinxem1 : sin x = -1
  rw [sin_eq_neg_one_iff] at sinxem1
  left
  obtain ⟨k,hk⟩ := sinxem1
  use k
  rw [← hk]; ring
  have sinxinm10 : -1 < sin x ∧ sin x < 0 := by 
    push_neg at sinpos sine0 sinxem1
    have : -1 ≤ sin x := by exact neg_one_le_sin x
    constructor
    exact lt_of_le_of_ne this (id (Ne.symm sinxem1))
    exact lt_of_le_of_ne sinpos sine0
  
  exfalso
  have cla: cos x ^ n - sin x ^ n < 1 := by 
    have t1 : cos x ^ n - sin x ^ n ≤ |cos x ^ n - sin x ^ n| := by exact le_abs_self (cos x ^ n - sin x ^ n)
    have t2 : |cos x ^ n - sin x ^ n| ≤ |cos x ^n| + |sin x ^n| := by exact abs_sub (cos x ^ n) (sin x ^ n)
    have t3 : |cos x ^n| ≤ cos x ^2 := by 
      have l1 : |cos x ^n| = |cos x| ^ n := by exact abs_pow (cos x) n
      have l2 : cos x ^2 = |cos x| ^2 := by exact Eq.symm (sq_abs (cos x))
      rw [l1,l2]
      have exi : ∃ m, 2 + m = n := by use n-2 ; omega
      obtain ⟨m,hm⟩ := exi
      rw [← hm]; rw [pow_add]
      have : |cos x| ^ m ≤ 1 := by 
        have : |cos x| ≤ 1 := by exact abs_cos_le_one x
        refine (pow_le_one_iff_of_nonneg ?_ ?_).mpr this
        exact abs_nonneg (cos x)
        omega
      nlinarith
    have t4 : |sin x ^n| < sin x ^2 := by 
      have l1 : |sin x ^n| = |sin x| ^ n := by exact abs_pow (sin x) n
      have l2 : sin x ^2 = |sin x| ^2 := by exact Eq.symm (sq_abs (sin x))
      rw [l1,l2]
      have exi : ∃ m, 2 + m = n := by use n-2 ; omega
      obtain ⟨m,hm⟩ := exi
      rw [← hm]; rw [pow_add]
      have : 0 < sin x ^2 := by nlinarith
      have : |sin x| ^ m < 1 := by 
        have : |sin x| < 1 := by nlinarith
        refine (pow_lt_one_iff_of_nonneg ?_ ?_).mpr this
        exact abs_nonneg (sin x)
        omega
      nlinarith
    have t5 : cos x ^ 2 + sin x ^ 2 =1 := by exact cos_sq_add_sin_sq x
    linarith
  simp [h] at cla



  --From right to left. Simple calculation using the properties of sin and cos.
  intro h
  rcases h with h | h

  --Even n and x = mπ.
  obtain ⟨evenn, h⟩ := h
  obtain ⟨m,hm⟩ := h
  simp [hm]
  field_simp
  obtain ⟨k,hk⟩ := evenn
  ring_nf at hk; rw [mul_comm] at hk
  rw [hk]
  rw [pow_mul]
  have : (cos (m*π))^2 = 1 := by 
    have : sin (m * π) = 0 := by exact sin_int_mul_pi m
    have sin2: (sin (m * π))^2 = 0 := by rw [this]; simp
    have eq: (cos (m*π))^2 = 1 - (sin (m * π))^2 := by exact cos_sq' (m * π)
    rw [sin2] at eq
    simp [eq]
  rw [this]
  simp

  --Odd n and x = 2mπ or 2mx - π/2
  obtain ⟨oddn, h⟩ := h
  rcases h with h | h
  obtain ⟨m,hm⟩ := h
  simp [hm]
  have coseq : cos (-π / 2)  = 0 := by 
    have : -π/2 = - (π/2) := by ring
    rw [this]
    simp
  have sineq : sin (-π / 2) = -1 := by 
    have : -π/2 = - (π/2) := by ring
    rw [this]
    simp
  simp [oddn, coseq, sineq]
  omega
  obtain ⟨m,hm⟩ := h
  simp [hm]
  rw [sin_eq_zero_iff]
  constructor
  use 2*m
  have : @Int.cast ℝ instIntCast (2 * m) = 2 * m := by norm_cast
  rw [this]
  ring
  omega
  