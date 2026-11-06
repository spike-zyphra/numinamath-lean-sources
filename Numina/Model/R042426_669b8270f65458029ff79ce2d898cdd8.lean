import Mathlib

open Matrix Complex

theorem calculus_11406 {a b c : ℂ} (M : Matrix (Fin 3) (Fin 3) ℂ)
    (hM : M ^ 2 = 1) (hM1 : M = !![a, b, c; b, c, a; c, a, b]) (hM2 : a * b * c = 1) :
    a ^ 3 + b ^ 3 + c ^ 3 = 2 ∨ a ^ 3 + b ^ 3 + c ^ 3 = 4 := by
  have eq1 := congr_fun hM 0
  have eq11 := congr_fun eq1 0
  have eq12 := congr_fun eq1 1
  have eq13 := congr_fun eq1 2

  have eq2 := congr_fun hM 1
  have eq21 := congr_fun eq2 0
  have eq22 := congr_fun eq2 1
  have eq23 := congr_fun eq2 2

  have eq3 := congr_fun hM 2
  have eq31 := congr_fun eq3 0
  have eq32 := congr_fun eq3 1
  have eq33 := congr_fun eq3 2

  simp [hM1, pow_two, Matrix.mul_apply, Fin.sum_univ_three, mul_add, add_mul] at eq11 eq12 eq13 eq21 eq22 eq23 eq31 eq32 eq33

  norm_num [pow_two] at eq11 eq12 eq13 eq21 eq22 eq23 eq31 eq32 eq33
  
  have h3 : a ^ 2 + b ^ 2 + c ^ 2 = (1 : ℂ) := by
    have eq11' : a * a + b * b + c * c = 1 := eq11
    have eq11'' : a * a + b * b + c * c = a ^ 2 + b ^ 2 + c ^ 2 := by ring_nf
    rw [eq11''] at eq11'
    tauto
  
  have h4 : (a + b + c) ^ 2 = (1 : ℂ) := by
    have eq11' : a ^ 2 + b ^ 2 + c ^ 2 = 1 := by
      exact_mod_cast h3
    have eq12' : a * b + b * c + c * a = 0 := by
      ring_nf at eq12 ⊢
      exact_mod_cast eq12
    have h4 : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by
      ring 
    rw [h4, eq11', eq12']
    all_goals norm_num
  
  have h5 : a + b + c = (1 : ℂ) ∨ a + b + c = (-1 : ℂ) := by
    have h : (a + b + c) ^ 2 = 1 := h4
    have h6 : (a + b + c) ^ 2 - (1 : ℂ) = 0 := by
      rw [h]
      all_goals norm_num 
    have h7 : ((a + b + c) - (1 : ℂ)) * ((a + b + c) + (1 : ℂ)) = 0 := by
      ring_nf at h6 ⊢
      exact_mod_cast h6
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- case ((a + b + c) - 1) = 0 
      left 
      exact_mod_cast eq_of_sub_eq_zero h8
    · -- case ((a + b + c) + 1) = 0 
      right
      have : (a + b + c) = (-1 : ℂ) := by 
        have eq : (a + b + c) + (1 : ℂ) = 0 := h9 
        calc 
          (a + b + c) = (a + b + c) + (1 : ℂ) - (1 : ℂ) := by ring_nf 
          _ = 0 - (1 : ℂ) := by rw [eq]
          _ = (-1 : ℂ) := by ring_nf 
      exact_mod_cast this
  
  cases h5 with 
  | inl h5 =>
    -- case a + b + c = 1 
    have h10 : a ^ 3 + b ^ 3 + c ^ 3 = (4 : ℂ) := by
      have h6 : a + b + c = (1 : ℂ) := h5
      have eq12' : a * b + b * c + c * a = (0 : ℂ) := by 
        ring_nf at eq12 ⊢ 
        exact_mod_cast eq12
      have eq11' : a * b * c = (1 : ℂ) := by
        exact_mod_cast hM2 
      calc 
        a ^ 3 + b ^ 3 + c ^ 3 = (a + b + c) ^ 3 - 3 * (a + b + c) * (a * b + b * c + c * a) + 3 * (a * b * c) := by 
          ring_nf 
        _ = (1 : ℂ) ^ 3 - 3 * (1 : ℂ) * (0 : ℂ) + 3 * (1 : ℂ) := by 
          rw [h6, eq12', eq11']
        _ = (4 : ℂ) := by 
          simp [pow_three]
          <;> ring_nf <;> norm_num
    right 
    tauto
  | inr h5 =>
    -- case a + b + c = -1 
    have h10 : a ^ 3 + b ^ 3 + c ^ 3 = (2 : ℂ) := by
      have h6 : a + b + c = (-1 : ℂ) := h5
      have eq12' : a * b + b * c + c * a = (0 : ℂ) := by 
        ring_nf at eq12 ⊢ 
        exact_mod_cast eq12
      have eq11' : a * b * c = (1 : ℂ) := by
        exact_mod_cast hM2 
      calc 
        a ^ 3 + b ^ 3 + c ^ 3 = (a + b + c) ^ 3 - 3 * (a + b + c) * (a * b + b * c + c * a) + 3 * (a * b * c) := by
          ring_nf 
        _ = (-1 : ℂ) ^ 3 - 3 * (-1 : ℂ) * (0 : ℂ) + 3 * (1 : ℂ) := by 
          rw [h6, eq12', eq11']
        _ = (2 : ℂ) := by
          simp [pow_three]
          <;> ring_nf <;> norm_num 
    left
    tauto