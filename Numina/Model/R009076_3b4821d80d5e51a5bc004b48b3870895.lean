import Mathlib

theorem algebra_16011 {f : ℕ → ℤ} (h : ∀ x y, 0 < x → 0 < y → f (x * y) = f x + f y)
    (h10 : f 10 = 14) (h40 : f 40 = 20) : f 500 = 39 := by
  have h4 : f 4 = 6 := by
    have h40_eq : f 40 = f 4 + f 10 := h 4 10 (by norm_num) (by norm_num)
    rw [h10, h40] at h40_eq
    omega
  
  have h25 : f 2 + f 5 = 14 := by
    have h10_eq : f 10 = f 2 + f 5 := h 2 5 (by norm_num) (by norm_num)
    rw [h10] at h10_eq
    omega
  
  have h20 : f 20 = f 2 + 14 := by
    have h20_eq : f 20 = f 2 + f 10 := h 2 10 (by norm_num) (by norm_num)
    rw [h10] at h20_eq
    linarith
  
  have h2 : f 2 = 3 := by
    have h40_eq : f 40 = f 2 + f 20 := h 2 20 (by norm_num) (by norm_num)
    rw [show f 20 = f 2 + 14 by
        omega
    ] at h40_eq
    rw [h40] at h40_eq
    omega
  
  have h5 : f 5 = 11 := by
    omega
  
  have h100 : f 100 = 28 := by
    have h100_eq : f 100 = f 10 + f 10 := by
      specialize h 10 10 (by norm_num) (by norm_num)
      norm_num at h ⊢
      linarith
    rw [h10] at h100_eq
    linarith
  
  have h500 : f 500 = f 100 + f 5 := h 100 5 (by norm_num) (by norm_num)
  
  rw [h100, h5] at h500
  linarith