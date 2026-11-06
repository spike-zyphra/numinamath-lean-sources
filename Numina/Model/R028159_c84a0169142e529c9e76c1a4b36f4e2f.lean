import Mathlib

theorem number_theory_111220 (A : Set ℕ) (hA : 2 ∈ A) (hA' : ∀ x ∈ A, 4 * x ∈ A)
    (hA'' : ∀ x, 9 * x + 11 ∈ A → x ∈ A) : 13 ∈ A := by 
  have h1 : 8 ∈ A := by
    specialize hA' 2 hA
    norm_num at hA' ⊢
    tauto
  have h2 : 32 ∈ A := by
    specialize hA' 8 h1
    norm_num at hA' ⊢
    tauto
  have h3 : 128 ∈ A := by
    specialize hA' 32 h2
    norm_num at hA' ⊢
    tauto 
  have h5 : 13 ∈ A := by
    have h6 : 9 * 13 + 11 ∈ A := by 
      norm_num at h3 ⊢ 
      tauto 
    specialize hA'' 13 h6 
    tauto 
  exact h5