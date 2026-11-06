import Mathlib

theorem number_theory_4004 (f : ℕ → ℕ) (h₀ : ∀ x y, 0 < x → 0 < y → f x + f y = f (x * y)) (h₁ : ∀ x, 0 < x → (x % 10 = 6 → f x = 0)) (h₂ : f 1920 = 420) : f 2015 = 420 := by
  have h3 : f 6 = 0 := by
    apply h₁ 6 (by norm_num) 
    all_goals norm_num
  have h4 : f 2 + f 3 = f 6 := by 
    have h5 : f 2 + f 3 = f (2 * 3) := by 
      apply h₀ 2 3 (by norm_num) (by norm_num)
    have h6 : 2 * 3 = 6 := by norm_num
    rw [h6] at h5 
    linarith
  have hf2 : f 2 = 0 := by 
    omega
  have hf3 : f 3 = 0 := by 
    omega
  have hf5 : f 5 = 420 := by 
    have h7 : f 384 + f 5 = f 1920 := by 
      have h8 : f 384 + f 5 = f (384 * 5) := by 
        apply h₀ 384 5 (by norm_num) (by norm_num)
      have h9 : 384 * 5 = 1920 := by norm_num
      rw [h9] at h8 
      linarith
    have h7' : f 384 = 0 := by
      have h70 : f 384 = f 2 + f 192 := by
        have h71 : f 2 + f 192 = f (2 * 192) := by
          apply h₀ 2 192 (by norm_num) (by norm_num)
        have h72 : 2 * 192 = 384 := by norm_num
        rw [h72] at h71 
        linarith
      have h71 : f 192 = f 2 + f 96 := by
        have h72 : f 2 + f 96 = f (2 * 96) := by
          apply h₀ 2 96 (by norm_num) (by norm_num)
        have h73 : 2 * 96 = 192 := by norm_num
        rw [h73] at h72 
        linarith
      have h72 : f 96 = f 2 + f 48 := by
        have h73 : f 2 + f 48 = f (2 * 48) := by
          apply h₀ 2 48 (by norm_num) (by norm_num)
        have h74 : 2 * 48 = 96 := by norm_num
        rw [h74] at h73 
        linarith
      have h73 : f 48 = f 2 + f 24 := by
        have h74 : f 2 + f 24 = f (2 * 24) := by
          apply h₀ 2 24 (by norm_num) (by norm_num)
        have h75 : 2 * 24 = 48 := by norm_num
        rw [h75] at h74 
        linarith
      have h74 : f 24 = f 2 + f 12 := by
        have h75 : f 2 + f 12 = f (2 * 12) := by
          apply h₀ 2 12 (by norm_num) (by norm_num)
        have h76 : 2 * 12 = 24 := by norm_num
        rw [h76] at h75 
        linarith
      have h75 : f 12 = f 2 + f 6 := by
        have h76 : f 2 + f 6 = f (2 * 6) := by
          apply h₀ 2 6 (by norm_num) (by norm_num)
        have h77 : 2 * 6 = 12 := by norm_num
        rw [h77] at h76 
        linarith
      omega
    omega
  have h13 : f 13 = 0 := by
    have h70 : f 2 + f 13 = f 26 := by
      have h71 : f 2 + f 13 = f (2 * 13) := by
        apply h₀ 2 13 (by norm_num) (by norm_num)
      have h72 : 2 * 13 = 26 := by norm_num
      rw [h72] at h71 
      linarith
    have hf26 : f 26 = 0 := by
      apply h₁ 26 (by norm_num) 
      all_goals norm_num
    omega
  have h31 : f 31 = 0 := by
    have hf186 : f 186 = 0 := by
      apply h₁ 186 (by norm_num) 
      all_goals norm_num
    have h70 : f 31 + f 6 = f 186 := by
      have h71 : f 31 + f 6 = f (31 * 6) := by
        apply h₀ 31 6 (by norm_num) (by norm_num)
      have h72 : 31 * 6 = 186 := by norm_num
      rw [h72] at h71 
      linarith
    omega
  have h2015 : f 2015 = f 5 + f 403 := by 
    have h70 : f 5 + f 403 = f (5 * 403) := by 
      apply h₀ 5 403 (by norm_num) (by norm_num)
    have h71 : 5 * 403 = 2015 := by norm_num
    rw [h71] at h70 
    linarith
  have hf403 : f 403 = 0 := by 
    have h70 : f 13 + f 31 = f 403 := by 
      have h71 : f 13 + f 31 = f (13 * 31) := by 
        apply h₀ 13 31 (by norm_num) (by norm_num)
      have h72 : 13 * 31 = 403 := by norm_num
      rw [h72] at h71 
      linarith
    omega
  omega