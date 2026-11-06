import Mathlib

theorem number_theory_98077 (meganNext meganNow: ℕ) (hmeganNow: meganNow = 15951) (hmeganNext: IsLeast {n:ℕ | n > meganNow ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n)} meganNext) :
(meganNext - meganNow) / 2 = 55 := by
  rw [hmeganNow] at hmeganNext ⊢
  have h1 : meganNext > 15951 := by
    have h2 := hmeganNext.left
    norm_num at h2 ⊢
    all_goals omega
  have h2 : Nat.digits 10 meganNext = List.reverse (Nat.digits 10 meganNext) := by 
    have h1 : meganNext ∈ {n:ℕ | n > 15951 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n)} := hmeganNext.left 
    simp at h1 ⊢ 
    tauto 
  have h3 : meganNext ≤ 16061 := by
    by_contra h
    push_neg at h
    have h4 : Nat.digits 10 meganNext = List.reverse (Nat.digits 10 meganNext) := by 
      have h1 : meganNext ∈ {n:ℕ | n > 15951 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n)} := hmeganNext.left 
      simp at h1 ⊢ 
      tauto 
    have h5 : meganNext ≥ 16062 := by 
      omega 
    have h6 : Nat.digits 10 (16061) = List.reverse (Nat.digits 10 (16061)) := by
      norm_num 
      <;> native_decide 
    have h7 : 16061 ∈ {n : ℕ | n > 15951 ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n)} := by
      constructor 
      · norm_num 
      · exact h6 
    have h8 : 16061 ≥ meganNext := by
      apply hmeganNext.2
      exact h7
    omega 
  -- Prove that it's greater or equal
  have h4 : meganNext ≥ 16061 := by
    by_contra h
    push_neg at h
    interval_cases meganNext <;> norm_num at h1 h2 ⊢ 
      <;> try { contradiction } <;> omega 
    <;> try { contradiction } <;> omega 
  have h5 : meganNext = 16061 := by 
    omega 
  -- Final calculation 
  calc 
    (meganNext - 15951) / 2 = (16061 - 15951) / 2 := by rw [h5]
    _ = 110 / 2 := by norm_num 
    _ = 55 := by norm_num 
  all_goals try { omega } <;> try { contradiction } <;> try { trivial }