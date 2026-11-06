import Mathlib

open Real 


theorem Algebra_608307 {x y : ℝ} (h : (x + y) ^ 2 = (x + 1) * (y - 1)) : x = - 1 ∧ y = 1 := by 
  -- change p = x + 1 ∧ q = y - 1 we get (p+q)^2= p*q => p=q=0 which means x=-1 and y=1
  let p := x + 1
  let q := y - 1
  have eq_aux : x = p - 1 := by 
    unfold p
    simp
  have eq_aux' : y = q + 1 := by 
    unfold q
    simp
  rw [eq_aux, eq_aux'] at h
  ring_nf at h
  have h_eq' : (x * y * 2 + x ^ 2 + y ^ 2) + 1 + x - x * y - y  = 0:= by 
    rw [h]
    ring
  have h_eq : p ^ 2 + p * q + q ^ 2 = 0 := by 
    rw [←h_eq']
    ring_nf
  -- p ^ 2 + p * q + q ^ 2 = (p + q / 2) ^ 2 + (3 / 4) * q ^ 2 => p + q/ 2= 0 ∧ q^2 * 3/4 = 0  so that we can solve p and q.
  have h_eqsq : p ^ 2 + p * q + q ^ 2 = (p + q / 2) ^ 2 + (3 / 4) * q ^ 2:= by 
    field_simp
    ring
  rw [h_eqsq] at h_eq
  have pnneg₁ : (p + q / 2) ^ 2 ≥ 0 := by positivity
  have pnneg₂ : (3 / 4) * q ^ 2 ≥ 0 := by positivity 
  have eq_aux₁ : (p + q / 2) ^ 2 = - (3 / 4) * q ^ 2 := by 
    rw [←add_zero (- (3 / 4) * q ^ 2), ←h_eq]
    ring
  have ineq_aux : - (3 / 4) * q ^ 2 ≥ 0 := by
    linarith
  have ineq_aux' : (3 / 4) * q ^ 2 ≤ 0 := by linarith
  have eq_zero₁ : (3 / 4) * q ^ 2 = 0 := le_antisymm ineq_aux' pnneg₂
  rw [eq_zero₁] at h_eq
  simp at h_eq
  simp at eq_zero₁
  constructor
  · rw [eq_zero₁] at h_eq
    simp at h_eq
    unfold p at h_eq
    rw [← add_zero (-1), ← h_eq]
    ring
  · unfold q at eq_zero₁
    rw [← add_zero (1), ← eq_zero₁]
    ring
