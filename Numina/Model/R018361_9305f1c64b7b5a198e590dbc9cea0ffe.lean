import Mathlib

theorem number_theory_111925 (A : Set ℕ) (hA : 2 ∈ A) (hA' : 3 ∈ A)
    (hA'' : ∀ x ∈ A, 4 * x ∈ A) (hA''' : ∀ x, 5 * x - 2 ∈ A → x ∈ A) :
    26 ∈ A ∧ 154 ∈ A := by 
  have h8 : 8 ∈ A := by
    specialize hA'' 2 hA
    norm_num at hA''
    exact hA''
  have h32 : 32 ∈ A := by
    specialize hA'' 8 h8
    norm_num at hA''
    exact hA''
  have h128 : 128 ∈ A := by 
    specialize hA'' 32 h32
    norm_num at hA''
    exact hA''
  have h26 : 26 ∈ A := by
    have h128' : 5 * 26 - 2 ∈ A := by
      have h2 : 5 * 26 - 2 = 128 := by
        omega 
      rw [h2]
      exact h128
    apply hA''' 26 
    exact h128'
  have h12 : 12 ∈ A := by 
    specialize hA'' 3 hA'
    norm_num at hA''
    exact hA''
  have h48 : 48 ∈ A := by 
    specialize hA'' 12 h12 
    norm_num at hA''
    exact hA''
  have h192 : 192 ∈ A := by 
    specialize hA'' 48 h48 
    norm_num at hA''
    exact hA''
  have h768 : 768 ∈ A := by
    specialize hA'' 192 h192 
    norm_num at hA''
    exact hA''
  have h154 : 154 ∈ A := by 
    have h768' : 5 * 154 - 2 ∈ A := by
      have h2 : 5 * 154 - 2 = 768 := by 
        omega 
      rw [h2] 
      exact h768 
    apply hA''' 154 
    exact h768' 
  exact ⟨h26, h154⟩