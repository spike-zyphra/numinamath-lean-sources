import Mathlib

theorem number_theory_184909 (a b : ℕ) (h₀ : ∃ n, a + b + 41 = n^2)
    (h₁ : ∃ m, a + b = m^2) (h₂ : ∃ p, a + 41 = p^2) (h₃ : ∃ q, b + 41 = q^2) :
    (a = 80 ∧ b = 320) ∨ (a = 320 ∧ b = 80) := by
  rcases h₀ with ⟨n, h0⟩
  rcases h₁ with ⟨m, h1⟩
  rcases h₂ with ⟨p, h2⟩
  rcases h₃ with ⟨q, h3⟩
  have eq1 : n^2 = m^2 + 41 := by
    have eq2 : a + b = m^2 := by
      linarith
    have eq3 : a + b + 41 = n^2 := by
      linarith
    linarith [eq2, eq3]
  have eq2 : n > m := by
    by_contra h
    push_neg at h
    have : n ≤ m := by linarith
    have : n^2 ≤ m^2 := by nlinarith
    nlinarith
  have eq4 : (n : ℤ) ^ 2 - (m : ℤ) ^ 2 = 41 := by
    zify at eq1
    linarith
  have eq5 : ((n : ℤ) - (m : ℤ)) * ((n : ℤ) + (m : ℤ)) = 41 := by
    nlinarith
  have h4 : ((n : ℤ) - (m : ℤ)) ∣ 41 := by
    use ((n : ℤ) + (m : ℤ))
    all_goals
      linarith [eq5]
  have h6 : ((n : ℤ) - (m : ℤ)) ≤ 41 := by
    apply Int.le_of_dvd (by norm_num) h4
  have h7 : ((n : ℤ) - (m : ℤ)) ≥ -41 := by
    have h8 : - ((n : ℤ) - (m : ℤ)) ∣ 41 := by
      exact Int.neg_dvd.2 h4
    have h9 : - ((n : ℤ) - (m : ℤ)) ≤ 41 := by
      apply Int.le_of_dvd (by norm_num) h8
    linarith
  have eq6 : (n : ℤ) = 21 := by
    interval_cases h : ((n : ℤ) - (m : ℤ)) <;> omega
  have eq7 : (m : ℤ) = 20 := by
    interval_cases h : ((n : ℤ) - (m : ℤ)) <;> omega
  have hn : n = 21 := by
    omega
  have hm : m = 20 := by
    omega
  have h8 : a + b = 400 := by
    have h9 : a + b = m^2 := by
      linarith
    rw [hm] at h9
    nlinarith
  have eq3 : p^2 + q^2 = 482 := by
    have eq4 : a + 41 = p^2 := by
      linarith
    have eq5 : b + 41 = q^2 := by
      linarith
    have eq6 : a + b = 400 := h8
    nlinarith
  have h9 : p ≤ 21 := by
    nlinarith
  have h10 : q ≤ 21 := by
    nlinarith
  interval_cases p <;> try { 
    omega
  } <;> try { 
    interval_cases q <;> 
    omega
  }