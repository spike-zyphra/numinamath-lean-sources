import Mathlib

theorem number_theory_115838 (a d : ℤ) (h : d > 0) (h1 : 25 ∈ {x | ∃ n, x = a + d * n}) (h2 : 41 ∈ {x | ∃ n, x = a + d * n}) (h3 : 65 ∈ {x | ∃ n, x = a + d * n}) :
    2017 ∈ {x | ∃ n, x = a + d * n} := by
  simp only [Set.mem_setOf_eq] at h1 h2 h3 ⊢
  rcases h1 with ⟨n1, h1⟩
  rcases h2 with ⟨n2, h2⟩
  rcases h3 with ⟨n3, h3⟩
  have eq1 : d * (n2 - n1) = 16 := by
    linarith
  have eq2 : d * (n3 - n1) = 40 := by 
    nlinarith
  have h4 : d ∣ 16 := by 
    use (n2 - n1)
    all_goals linarith 
  have h5 : d ∣ 40 := by 
    use (n3 - n1)
    all_goals linarith 
  have h6 : d ∣ 8 := by 
    exact Int.dvd_gcd h4 h5
  have h7 : d ≤ 8 := by 
    exact Int.le_of_dvd (by norm_num) h6 
  have h8 : d ≥ 1 := by 
    linarith 
  have h9 : d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 8 := by 
    interval_cases d <;> try tauto
  rcases h9 with (r | r | r | r)
  · -- Case d = 1
    have h10 : d = 1 := by 
      linarith 
    refine' ⟨2017 - a, by 
      rw [show d = 1 by linarith]
      all_goals 
        linarith 
    ⟩
  · -- Case d = 2
    have h10 : d = 2 := by 
      linarith 
    have eq3 : a = 25 - 2 * n1 := by
      have eq4 : (25 : ℤ) = a + 2 * n1 := by 
        rw [show d = 2 by linarith] at h1 
        linarith 
      linarith
    use n1 + 996 
    rw [show d = 2 by linarith] 
    rw [eq3] 
    all_goals 
      linarith
  · -- Case d = 4
    have h10 : d = 4 := by 
      linarith 
    have eq3 : a = 25 - 4 * n1 := by
      have eq4 : (25 : ℤ) = a + 4 * n1 := by 
        rw [show d = 4 by linarith] at h1 
        linarith 
      linarith 
    use 498 + n1 
    rw [show d = 4 by linarith] 
    rw [eq3] 
    all_goals 
      linarith 
  · -- Case d = 8
    have h10 : d = 8 := by 
      linarith 
    have eq3 : a = 25 - 8 * n1 := by
      have eq4 : (25 : ℤ) = a + 8 * n1 := by 
        rw [show d = 8 by linarith] at h1 
        linarith 
      linarith 
    use 249 + n1 
    rw [show d = 8 by linarith] 
    rw [eq3] 
    all_goals 
      linarith