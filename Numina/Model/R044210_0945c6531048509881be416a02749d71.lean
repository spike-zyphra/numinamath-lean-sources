import Mathlib

open Real

theorem number_theory_183951 :
    Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1000} = 3149 ∧ 
    Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 999} = 3133 ∧
    Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 998} = 3133 ∧
    Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 997} = 3133 ∧ 
    Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 996} = 3125 ∧ 
    Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 995} = 3125 ∧ 
    Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1001} = 3149 ∧ 
    Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1002} = 3149 ∧ 
    Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1003} = 3149 ∧ 
    Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1004} = 3149 ∧ 
    Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1005} = 3149
    := by 
  have h1 : Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1000} = 3149 := by
    have h2 : {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1000} = Finset.filter (fun p : ℤ × ℤ => p.1^2 + p.2^2 ≤ 1000) (Finset.Icc (-31 : ℤ) 31 ×ˢ Finset.Icc (-31 : ℤ) 31) := by
      ext ⟨x, y⟩
      simp
      intro h
      have h2 : x ≥ -31 := by nlinarith
      have h3 : x ≤ 31 := by nlinarith
      have h4 : y ≥ -31 := by nlinarith
      have h5 : y ≤ 31 := by nlinarith
      omega
    rw [h2]
    rw [Set.ncard_coe_Finset]
    native_decide
  have h2 : Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 999} = 3133 := by
    have h3 : {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 999} = Finset.filter (fun p : ℤ × ℤ => p.1^2 + p.2^2 ≤ 999) (Finset.Icc (-31 : ℤ) 31 ×ˢ Finset.Icc (-31 : ℤ) 31) := by
      ext ⟨x, y⟩
      simp
      intro h
      have h2 : x ≥ -31 := by nlinarith
      have h3 : x ≤ 31 := by nlinarith
      have h4 : y ≥ -31 := by nlinarith
      have h5 : y ≤ 31 := by nlinarith
      omega
    rw [h3]
    rw [Set.ncard_coe_Finset]
    native_decide
  have h3 : Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 998} = 3133 := by
    have h4 : {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 998} = Finset.filter (fun p : ℤ × ℤ => p.1^2 + p.2^2 ≤ 998) (Finset.Icc (-31 : ℤ) 31 ×ˢ Finset.Icc (-31 : ℤ) 31) := by
      ext ⟨x, y⟩
      simp
      intro h
      have h2 : x ≥ -31 := by nlinarith
      have h3 : x ≤ 31 := by nlinarith
      have h4 : y ≥ -31 := by nlinarith
      have h5 : y ≤ 31 := by nlinarith
      omega
    rw [h4]
    rw [Set.ncard_coe_Finset]
    native_decide
  have h4 : Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 997} = 3133 := by
    have h5 : {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 997} = Finset.filter (fun p : ℤ × ℤ => p.1^2 + p.2^2 ≤ 997) (Finset.Icc (-31 : ℤ) 31 ×ˢ Finset.Icc (-31 : ℤ) 31) := by
      ext ⟨x, y⟩
      simp
      intro h
      have h2 : x ≥ -31 := by nlinarith
      have h3 : x ≤ 31 := by nlinarith
      have h4 : y ≥ -31 := by nlinarith
      have h5 : y ≤ 31 := by nlinarith
      omega
    rw [h5]
    rw [Set.ncard_coe_Finset]
    native_decide
  have h5 : Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 996} = 3125 := by
    have h6 : {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 996} = Finset.filter (fun p : ℤ × ℤ => p.1^2 + p.2^2 ≤ 996) (Finset.Icc (-31 : ℤ) 31 ×ˢ Finset.Icc (-31 : ℤ) 31) := by
      ext ⟨x, y⟩
      simp
      intro h
      have h2 : x ≥ -31 := by nlinarith
      have h3 : x ≤ 31 := by nlinarith
      have h4 : y ≥ -31 := by nlinarith
      have h5 : y ≤ 31 := by nlinarith
      omega
    rw [h6]
    rw [Set.ncard_coe_Finset]
    native_decide
  have h6 : Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 995} = 3125 := by
    have h7 : {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 995} = Finset.filter (fun p : ℤ × ℤ => p.1^2 + p.2^2 ≤ 995) (Finset.Icc (-31 : ℤ) 31 ×ˢ Finset.Icc (-31 : ℤ) 31) := by
      ext ⟨x, y⟩
      simp
      intro h
      have h2 : x ≥ -31 := by nlinarith
      have h3 : x ≤ 31 := by nlinarith
      have h4 : y ≥ -31 := by nlinarith
      have h5 : y ≤ 31 := by nlinarith
      omega
    rw [h7]
    rw [Set.ncard_coe_Finset]
    native_decide
  have h7 : Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1001} = 3149 := by
    have h8 : {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1001} = Finset.filter (fun p : ℤ × ℤ => p.1^2 + p.2^2 ≤ 1001) (Finset.Icc (-31 : ℤ) 31 ×ˢ Finset.Icc (-31 : ℤ) 31) := by
      ext ⟨x, y⟩
      simp
      intro h
      have h2 : x ≥ -31 := by nlinarith
      have h3 : x ≤ 31 := by nlinarith
      have h4 : y ≥ -31 := by nlinarith
      have h5 : y ≤ 31 := by nlinarith
      omega
    rw [h8]
    rw [Set.ncard_coe_Finset]
    native_decide
  have h8 : Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1002} = 3149 := by
    have h9 : {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1002} = Finset.filter (fun p : ℤ × ℤ => p.1^2 + p.2^2 ≤ 1002) (Finset.Icc (-31 : ℤ) 31 ×ˢ Finset.Icc (-31 : ℤ) 31) := by
      ext ⟨x, y⟩
      simp
      intro h
      have h2 : x ≥ -31 := by nlinarith
      have h3 : x ≤ 31 := by nlinarith
      have h4 : y ≥ -31 := by nlinarith
      have h5 : y ≤ 31 := by nlinarith
      omega
    rw [h9]
    rw [Set.ncard_coe_Finset]
    native_decide
  have h9 : Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1003} = 3149 := by
    have h10 : {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1003} = Finset.filter (fun p : ℤ × ℤ => p.1^2 + p.2^2 ≤ 1003) (Finset.Icc (-31 : ℤ) 31 ×ˢ Finset.Icc (-31 : ℤ) 31) := by
      ext ⟨x, y⟩
      simp
      intro h
      have h2 : x ≥ -31 := by nlinarith
      have h3 : x ≤ 31 := by nlinarith
      have h4 : y ≥ -31 := by nlinarith
      have h5 : y ≤ 31 := by nlinarith
      omega
    rw [h10]
    rw [Set.ncard_coe_Finset]
    native_decide
  have h10 : Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1004} = 3149 := by
    have h11 : {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1004} = Finset.filter (fun p : ℤ × ℤ => p.1^2 + p.2^2 ≤ 1004) (Finset.Icc (-31 : ℤ) 31 ×ˢ Finset.Icc (-31 : ℤ) 31) := by
      ext ⟨x, y⟩
      simp
      intro h
      have h2 : x ≥ -31 := by nlinarith
      have h3 : x ≤ 31 := by nlinarith
      have h4 : y ≥ -31 := by nlinarith
      have h5 : y ≤ 31 := by nlinarith
      omega
    rw [h11]
    rw [Set.ncard_coe_Finset
    ]
    native_decide
  have h11 : Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1005} = 3149 := by
    have h12 : {p : ℤ × ℤ | p.1^2 + p.2^2 ≤ 1005} = Finset.filter (fun p : ℤ × ℤ => p.1^2 + p.2^2 ≤ 1005) (Finset.Icc (-31 : ℤ) 31 ×ˢ Finset.Icc (-31 : ℤ) 31) := by
      ext ⟨x, y⟩
      simp
      intro h
      have h2 : x ≥ -31 := by nlinarith
      have h3 : x ≤ 31 := by nlinarith
      have h4 : y ≥ -31 := by nlinarith
      have h5 : y ≤ 31 := by nlinarith
      omega
    rw [h12
    ]
    rw [Set.ncard_coe_Finset]
    native_decide
  constructor
  · exact h1
  constructor
  · exact h2
  constructor
  · exact h3
  constructor
  · exact h4
  constructor
  · exact h5
  constructor
  · exact h6
  constructor
  · exact h7
  constructor
  · exact h8
  constructor
  · exact h9
  constructor
  · exact h10
  · exact h11
  all_goals try { tauto }