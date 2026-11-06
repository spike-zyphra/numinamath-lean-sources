import Mathlib

theorem number_theory_97765 
  (s1 s2 s3 s4 s5 s6 s7 : ℕ)
  (h_range1 : 91 ≤ s1 ∧ s1 ≤ 100)
  (h_range2 : 91 ≤ s2 ∧ s2 ≤ 100)
  (h_range3 : 91 ≤ s3 ∧ s3 ≤ 100)
  (h_range4 : 91 ≤ s4 ∧ s4 ≤ 100)
  (h_range5 : 91 ≤ s5 ∧ s5 ≤ 100)
  (h_range6 : 91 ≤ s6 ∧ s6 ≤ 100)
  (h_range7 : 91 ≤ s7 ∧ s7 ≤ 100)
  (h_distinct : s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s1 ≠ s5 ∧ s1 ≠ s6 ∧ s1 ≠ s7 ∧
                 s2 ≠ s3 ∧ s2 ≠ s4 ∧ s2 ≠ s5 ∧ s2 ≠ s6 ∧ s2 ≠ s7 ∧
                 s3 ≠ s4 ∧ s3 ≠ s5 ∧ s3 ≠ s6 ∧ s3 ≠ s7 ∧
                 s4 ≠ s5 ∧ s4 ≠ s6 ∧ s4 ≠ s7 ∧
                 s5 ≠ s6 ∧ s5 ≠ s7 ∧
                 s6 ≠ s7)
  (h_avg1 : ∃ a1 : ℕ, s1 = 1 * a1)
  (h_avg2 : ∃ a2 : ℕ, s1 + s2 = 2 * a2)
  (h_avg3 : ∃ a3 : ℕ, s1 + s2 + s3 = 3 * a3)
  (h_avg4 : ∃ a4 : ℕ, s1 + s2 + s3 + s4 = 4 * a4)
  (h_avg5 : ∃ a5 : ℕ, s1 + s2 + s3 + s4 + s5 = 5 * a5)
  (h_avg6 : ∃ a6 : ℕ, s1 + s2 + s3 + s4 + s5 + s6 = 6 * a6)
  (h_avg7 : ∃ a7 : ℕ, s1 + s2 + s3 + s4 + s5 + s6 + s7 = 7 * a7)
  (h_score7 : s7 = 95)
  : s6 = 100 := by

  have h1 : s1 ≤ 100 := h_range1.right
  have h2 : 91 ≤ s1 := h_range1.left
  have h3 : s2 ≤ 100 := h_range2.right
  have h4 : 91 ≤ s2 := h_range2.left
  have h5 : s3 ≤ 100 := h_range3.right
  have h6 : 91 ≤ s3 := h_range3.left
  have h7 : s4 ≤ 100 := h_range4.right
  have h8 : 91 ≤ s4 := h_range4.left
  have h9 : s5 ≤ 100 := h_range5.right
  have h10 : 91 ≤ s5 := h_range5.left
  have h11 : s6 ≤ 100 := h_range6.right
  have h12 : 91 ≤ s6 := h_range6.left
  have h13 : s7 ≤ 100 := h_range7.right
  have h14 : 91 ≤ s7 := h_range7.left
  have h15 : s7 = 95 := h_score7

  rcases h_avg1 with ⟨a1, ha1⟩
  rcases h_avg2 with ⟨a2, ha2⟩
  rcases h_avg3 with ⟨a3, ha3⟩
  rcases h_avg4 with ⟨a4, ha4⟩
  rcases h_avg5 with ⟨a5, ha5⟩
  rcases h_avg6 with ⟨a6, ha6⟩
  rcases h_avg7 with ⟨a7, ha7⟩

  have eq1 : 6 * a6 = 7 * a7 - 95 := by
    have h_eq1 : s1 + s2 + s3 + s4 + s5 + s6 = 6 * a6 := by
      omega
    have h_eq2 : s1 + s2 + s3 + s4 + s5 + s6 + s7 = 7 * a7 := by
      omega
    have h_eq3 : s7 = 95 := h15
    omega

  have h16 : a7 ≤ 95 := by 
    omega
  have h17 : a7 ≥ 94 := by 
    omega

  interval_cases a7 <;> try { 
    omega 
  } <;> try { 
    have h32 : False := by 
      omega 
    contradiction
  } <;> try { 
    omega 
  }