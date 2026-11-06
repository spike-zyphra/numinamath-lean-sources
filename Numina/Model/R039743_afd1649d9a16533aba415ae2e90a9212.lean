import Mathlib

theorem number_theory_188821 (n : ℤ) :
    ¬ ∃ m, m^2 = ∑ i ∈ Finset.range 5, (n + i)^2 := by 
  rintro ⟨m, hm⟩
  have h4 : ∑ i ∈ Finset.range 5, (n + i)^2 = 5 * n^2 + 20 * n + 30 := by 
    simp [Finset.sum_range_succ]
    ring_nf
  rw [h4] at hm
  have h5 : m ^ 2 % 4 = 0 ∨ m ^ 2 % 4 = 1 := by
    have h6 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
      omega 
    rcases h6 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.emod]
  
  have h7 : (5 * n^2 + 20 * n + 30) % 4 = 2 ∨ (5 * n^2 + 20 * n + 30) % 4 = 3 := by
    have eq1 : (5 * n^2 + 20 * n + 30) % 4 = (n^2 + 2) % 4 := by
      ring_nf
      <;> omega 
    rw [eq1]
    have h8 : (n^2 + 2) % 4 = 2 ∨ (n^2 + 2) % 4 = 3 := by
      have h9 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
        omega 
      rcases h9 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.emod]
    tauto
  
  have h8 : m ^ 2 % 4 = (5 * n^2 + 20 * n + 30) % 4 := by 
    omega

  omega