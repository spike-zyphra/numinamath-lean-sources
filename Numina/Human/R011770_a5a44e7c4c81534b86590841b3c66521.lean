import Mathlib

open Real

/-
2. Solve the equation $(\cos x-3 \cos 4 x)^{2}=16+\sin ^{2} 3 x$.
-/

theorem algebra_159382 (x:ℝ):
(cos x - 3 * cos (4*x))^2 = 16 +  (sin (3 * x))^2 
↔
∃ k : ℤ, x = Real.pi + k*(2*Real.pi) := by

  constructor
  intro h

  --We know that the abolsute value of sin and cos is less or equal to one, so from our assumption, we have sin 3x = 0.
  have b1: -1 ≤ cos x := by exact neg_one_le_cos x
  have b2: cos (4*x) ≤ 1 := by exact cos_le_one (4 * x)
  have b3: cos x ≤ 1 := by exact cos_le_one x
  have b4: -1 ≤ cos (4*x) := by exact neg_one_le_cos (4 * x)
  
  have t1 : |(cos x - 3 * cos (4*x))| ≤ 4 := by 
    rw [abs_le]
    constructor  
    linarith
    linarith
  have t2 : (cos x - 3 * cos (4*x))^2 ≤ 16 := by nlinarith
  have sin3x: (sin (3*x)) = 0 := by 
    by_contra ne
    have : 0 < (sin (3*x))^2 := by exact pow_two_pos_of_ne_zero ne
    linarith
    
  rw [sin_eq_zero_iff] at sin3x
  obtain ⟨n1,hn1⟩ := sin3x

  --Also |(cos x - 3 * cos (4*x))| = 4, so it has to be that (cos x = -1 ∧ cos (4*x) = 1) ∨ (cos x = 1 ∧ cos (4*x)=-1).
  have :  |(cos x - 3 * cos (4*x))| = 4 := by 
    have eq: (cos x - 3 * cos (4*x))^2 = 16 := by nlinarith
    have : (16:ℝ) = 4^2 := by norm_num
    rw [this] at eq
    rw [sq_eq_sq_iff_eq_or_eq_neg] at eq
    rw [abs_eq]
    exact eq
    norm_num
  have : (cos x = -1 ∧ cos (4*x) = 1) ∨ (cos x = 1 ∧ cos (4*x)=-1) := by
    rw [abs_eq] at this
    rcases this with hl | hr
    
    right
    constructor
    linarith
    linarith
    left
    constructor
    linarith
    linarith
    
    linarith
    
  --The remaining is just to use the values of sin and cos.
  rcases this with ⟨hx,h4x⟩ | ⟨hx,h4x⟩
  
  rw [cos_eq_neg_one_iff] at hx
  obtain ⟨n2,hn2⟩ := hx
  use n2
  nlinarith

  exfalso
  rw [cos_eq_one_iff] at hx
  obtain ⟨n2,hn2⟩ := hx
  rw [cos_eq_neg_one_iff] at h4x
  obtain ⟨n3,hn3⟩ := h4x
  rw [← hn2] at hn3
  ring_nf at hn3
  have pipos: 0<Real.pi := by exact pi_pos
  have pin0 : Real.pi ≠ 0 := by exact pi_ne_zero
  have : 1 + 2*n3 = 8 * n2 := by 
    rify
    have : Real.pi * (1+ n3 *2) = Real.pi *(n2 *8):= by nlinarith
    field_simp at this
    simp [pin0] at this
    linarith
  omega

  --From right to left, some simple verification.
  intro h
  obtain ⟨k,hk⟩ := h
  simp [hk]
  have : (4 * (π + ↑k * (2 * π))) = (4*k+2) * (2 * π) := by ring
  rw [this]
  norm_cast
  have : cos (↑(4 * k + 2) * (2 * π)) = 1 := by 
    rw [Real.cos_eq_one_iff]
    use 4*k+2
  rw [this]
  have : sin (3 * (π + ↑k * (2 * π))) = 0 := by 
    rw [sin_eq_zero_iff]
    use 6*k+3
    field_simp
    ring_nf
  rw [this]
  simp
  norm_num
  