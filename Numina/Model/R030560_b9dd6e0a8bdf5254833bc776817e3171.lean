import Mathlib

theorem algebra_212506 {f : ℕ → ℕ} (fpos : ∀ n, 0<n → 0<f (n)) (hf : ∀ n, 0 < n → f (f n) = 4 * n + 9) (hf' : ∀ k, 0 ≤ k → f (2 ^ k) = 2 ^ (k + 1) + 3) : f 1789 = 3581 := by
  have h1 : f 4 = 11 := by 
    specialize hf' 2 (by norm_num)
    norm_num at hf'
    exact_mod_cast hf'
  have h2 : f 11 = 25 := by 
    have h11 : 0 < 4 := by norm_num
    have h22 := hf 4 h11
    rw [h1] at h22
    norm_num at h22 ⊢
    exact_mod_cast h22
  have h3 : f 25 = 53 := by 
    have h11 : 0 < 11 := by norm_num
    have h22 := hf 11 h11
    rw [h2] at h22
    norm_num at h22 ⊢
    exact_mod_cast h22
  have h4 : f 53 = 109 := by 
    have h11 : 0 < 25 := by norm_num
    have h22 := hf 25 h11
    rw [h3] at h22
    norm_num at h22 ⊢
    exact_mod_cast h22
  have h5 : f 109 = 221 := by 
    have h11 : 0 < 53 := by norm_num
    have h22 := hf 53 h11
    rw [h4] at h22
    norm_num at h22 ⊢
    exact_mod_cast h22
  have h6 : f 221 = 445 := by 
    have h11 : 0 < 109 := by norm_num
    have h22 := hf 109 h11
    rw [h5] at h22
    norm_num at h22 ⊢
    exact_mod_cast h22
  have h7 : f 445 = 893 := by 
    have h11 : 0 < 221 := by norm_num
    have h22 := hf 221 h11
    rw [h6] at h22
    norm_num at h22 ⊢
    exact_mod_cast h22
  have h8 : f 893 = 1789 := by 
    have h11 : 0 < 445 := by norm_num
    have h22 := hf 445 h11
    rw [h7] at h22
    norm_num at h22 ⊢
    exact_mod_cast h22
  have h9 : f 1789 = 3581 := by 
    have h11 : 0 < 893 := by norm_num
    have h22 := hf 893 h11
    rw [h8] at h22
    norm_num at h22 ⊢
    exact_mod_cast h22
  exact_mod_cast h9