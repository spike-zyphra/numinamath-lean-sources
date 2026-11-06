import Mathlib

open Real

/-
11.6. Solve the equation

$$
\cos 2x - \sin 2x + 2 \cos x + 1 = 0
$$
-/

theorem algebra_165800 (x : ℝ):
cos (2*x) - sin (2*x) + 2 * cos x + 1 = 0 
↔ 
(∃ k : ℤ, -π /2 + k * (2*π) = x) ∨
(∃ k : ℤ,  π /2 + k * (2*π) = x) ∨
(∃ k : ℤ,  π    + k * (2*π) = x)
:= by

  --We rewrite the left-handed side and get it equals (sin x -1) * (sin x + cos + 1).
  rw [Real.cos_two_mul']
  rw [Real.cos_sq']
  rw [Real.sin_two_mul]
  have : 1 - sin x ^ 2 - sin x ^ 2 - 2 * sin x * cos x + 2 * cos x + 1 = -2 * (sin x - 1) * (sin x + cos x + 1) := by  
    rw [pow_two]; 
    ring
  rw [this]
  simp

  --Now we just need to check when these two terms equal zero separately.
  have e1 : sin x - 1 = 0 ↔ sin x = 1 := by 
    constructor
    intro h; linarith
    intro h; linarith
  rw [e1]
  rw [Real.sin_eq_one_iff]

  have e2 : sin x + cos x + 1 = 0 ↔  (∃ k : ℤ, -π/2 + ↑k * (2 * π) = x)  ∨ (∃ k : ℤ, π + ↑k * (2 * π) = x) := by 
    constructor

    intro h

    have tmp : sin (x + π /4) = sin x * cos (π/4) + cos x * sin (π/4) := by 
      exact sin_add x (π / 4)
    simp at tmp
    have tmp2 : sin (x + π/4) = - √2 /2 := by 
      rw [tmp]; field_simp; 
      rw [←add_mul]
      have : sin x + cos x = -1 := by linarith
      rw [this]
      ring
      
      
    have tmp3 : sin (- (π / 4)) = - √2 / 2 := by 
      have : sin (π /4) = √2 / 2 := by exact sin_pi_div_four
      have : sin (-(π /4)) = - sin (π /4) := by exact Real.sin_neg (π /4)
      linarith
    have eq : sin (-(π/4)) = sin (x+π/4) := by linarith
    rw [Real.sin_eq_sin_iff] at eq
    obtain ⟨k, eq⟩ := eq
    obtain eq | eq := eq
    left
    use k
    linarith
    right
    use k
    linarith

    intro h
    obtain h | h := h
    obtain ⟨k, hk⟩ := h
    have sinxe : sin x = -1 := by 
      rw [Real.sin_eq_neg_one_iff]
      use k
      linarith
    have cosxe : cos x =  0 := by 
      rw [Real.cos_eq_zero_iff]
      use (2*k-1)
      rw [← hk]
      ring_nf
      field_simp
      rw [mul_add]
      rw [add_mul]
      linarith
    linarith
    obtain ⟨k, hk⟩ := h
    have sinxe : sin x =  0 := by 
      rw [Real.sin_eq_zero_iff]
      use (2*k+1)
      rw [← hk]
      field_simp
      nlinarith
    have cosxe : cos x = -1 := by 
      rw [Real.cos_eq_neg_one_iff]
      use k
    linarith


  rw [e2]
    
  
  tauto
  