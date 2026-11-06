import Mathlib

open Nat

theorem number_theory_636425 (k : ℕ) (hk : 0 < k) (K₀ L₀ A₀ B₀ D₁ D₂ N A B: ℕ) 
  (Kpos : 0 < K₀) (Lpos : 0 < L₀) (h1 : K₀ % 2 = L₀ % 2) (h2 : L₀ > K₀) 
  (hA₀ : A₀ = (K₀ + L₀) / 2) (hB₀ : B₀ = (L₀ - K₀) / 2) (hD₁ : D₁ = (10 ^ k - 1) * K₀) (hD₂ : D₂ = K₀ * L₀) (hN : N = 10 ^ k * A + B) (hN1 : N = 10 ^ k * B + A + D₁) (hN2 : A ^ 2 - B ^ 2 = D₂) : N = 10 ^ k * A₀ + B₀ := by 
  have AgeB : A ^ 2 > B ^ 2 := by 
      have aux1 : A ^ 2 - B ^ 2 > 0 := by 
        rw [hN2, hD₂]
        positivity
      exact Nat.lt_of_sub_pos aux1
  have AgtB : A > B := by 
    exact lt_of_pow_lt_pow_left' 2 AgeB
  have eq1 : (A - B) * (10 ^ k - 1) = (10 ^ k - 1) * K₀ := by 
    rw [hN, hD₁] at hN1
    zify at hN1
    zify 
    rw [Nat.cast_sub, cast_sub]
    rw [cast_sub] at hN1
    norm_num at hN1 ⊢
    nlinarith
    exact one_le_pow' k 9
    exact one_le_pow' k 9
    linarith
  have neq : (10 ^ k - 1) ≠ 0 := by 
    have aux : 10 ^ k > 1 := by 
      refine (Nat.one_lt_pow_iff ?_).mpr ?_
      linarith
      linarith
    omega
  have pos : (10 ^ k - 1) > 0 := by 
    have aux : 10 ^ k > 1 := by 
      refine (Nat.one_lt_pow_iff ?_).mpr ?_
      linarith
      linarith
    omega
  have eq2 : A - B = K₀ := by
    conv at eq1 =>
      rhs
      rw [mul_comm]
    exact Eq.symm (eq_of_mul_eq_mul_right pos (id (Eq.symm eq1)))
  have eq3 : A + B = L₀ := by 
    have aux : (A - B) * (A + B) = D₂ := by 
      rw [←hN2]
      zify
      rw [cast_sub, cast_sub]
      norm_num
      ring
      linarith
      linarith
    rw [eq2, hD₂] at aux
    have kneq : K₀ ≠ 0 := by 
      linarith 
    exact Eq.symm (Nat.eq_of_mul_eq_mul_left Kpos (id (Eq.symm aux)))
  have Aeq : A = A₀ := by 
    rw [hA₀, ←eq2, ← eq3]
    zify
    rw [cast_sub]
    ring_nf 
    refine Eq.symm (Int.mul_ediv_cancel ↑A ?_)
    norm_num
    linarith
  have Beq : B = B₀ := by
    rw [hB₀, ← eq2, ← eq3]
    zify
    rw [cast_sub, cast_sub]
    norm_num
    ring_nf
    refine Eq.symm (Int.mul_ediv_cancel ↑B ?_)
    norm_num
    linarith
    omega
  rw [←Aeq, ←Beq, hN]