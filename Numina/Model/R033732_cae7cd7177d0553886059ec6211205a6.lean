import Mathlib

theorem number_theory_609051: {(d1, d2, d3) : ℕ × ℕ × ℕ | d1 * d2 * d3 ∣ 360}.encard = 800 := by
  have h1 : {(d1, d2, d3) : ℕ × ℕ × ℕ | d1 * d2 * d3 ∣ 360} = Finset.filter (fun s : ℕ × ℕ × ℕ => s.1 * s.2.1 * s.2.2 ∣ 360) (Finset.Icc (0 : ℕ) 360 ×ˢ Finset.Icc (0 : ℕ) 360 ×ˢ Finset.Icc (0 : ℕ) 360) := by
    ext ⟨d1, d2, d3⟩
    simp
    intro h
    have h4 : d1 ∣ 360 := by 
      have h7 : d1 * d2 * d3 ∣ 360 := h 
      have h8 : d1 ∣ d1 * d2 * d3 := by 
        use d2 * d3 
        ring 
      exact dvd_trans h8 h7 
    have h1 : d1 ≤ 360 := by 
      exact Nat.le_of_dvd (by norm_num) h4 
    have h5 : d2 ∣ 360 := by 
      have h7 : d1 * d2 * d3 ∣ 360 := h 
      have h9 : d2 ∣ d1 * d2 * d3 := by 
        use d1 * d3 
        ring 
      exact dvd_trans h9 h7 
    have h2 : d2 ≤ 360 := by 
      exact Nat.le_of_dvd (by norm_num) h5 
    have h6 : d3 ∣ 360 := by 
      have h7 : d1 * d2 * d3 ∣ 360 := h 
      have h10 : d3 ∣ d1 * d2 * d3 := by 
        use d1 * d2 
        ring 
      exact dvd_trans h10 h7 
    have h3 : d3 ≤ 360 := by 
      exact Nat.le_of_dvd (by norm_num) h6 
    simp [h1, h2, h3] 
    <;> try { tauto } 
  rw [h1] 
  rw [Set.encard_coe_eq_coe_finsetCard] 
  native_decide