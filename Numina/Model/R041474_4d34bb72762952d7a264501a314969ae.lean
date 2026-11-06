import Mathlib

theorem number_theory_115181 (n : ℤ) : ¬(121 ∣ n^2 + 2 * n + 12) := by 
  intro h 
  have h1 : (n ^ 2 + 2 * n + 12) % 121 = 0 := by 
    omega
  have h2 : (n ^ 2 + 2 * n + 12) % 11 = 0 := by 
    omega
  have h3 : n % 11 = 10 := by 
    have h2' : (n ^ 2 + 2 * n + 12) % 11 = 0 := by 
      omega 
    have h4 : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by 
      omega 
    rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> simp [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h4] at h2' <;> try { omega }
  have h4 : ∃ k : ℤ, n = 10 + 11 * k := by 
    have h5 : n % 11 = 10 := h3
    refine' ⟨(n - 10) / 11, by omega⟩
  rcases h4 with ⟨k, hk⟩
  have h5 : (n ^ 2 + 2 * n + 12) % 121 = 0 := by 
    omega
  rw [hk] at h5
  ring_nf at h5 
  all_goals omega