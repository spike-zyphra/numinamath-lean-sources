import Mathlib

theorem number_theory_196236 (n : ℕ) (a : Fin n → ℤ) :
    30 ∣ ∑ i : Fin n, a i → 30 ∣ ∑ i : Fin n, (a i)^5 := by 
  intro h
  have h1 : ∀ i : Fin n, (a i) ^ 5 % 30 = (a i) % 30 := by
    intro i
    have h1 : (a i) ^ 5 % 2 = (a i) % 2 := by
      have h1 : (a i) % 2 = 0 ∨ (a i) % 2 = 1 := by
        omega
      rcases h1 with (h1 | h1)
      ·
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
      ·
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
    have h2 : (a i) ^ 5 % 3 = (a i) % 3 := by
      have h1 : (a i) % 3 = 0 ∨ (a i) % 3 = 1 ∨ (a i) % 3 = 2 := by
        omega
      rcases h1 with (h1 | h1 | h1)
      ·
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
      ·
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
      ·
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
    have h3 : (a i) ^ 5 % 5 = (a i) % 5 := by
      have h1 : (a i) % 5 = 0 ∨ (a i) % 5 = 1 ∨ (a i) % 5 = 2 ∨ (a i) % 5 = 3 ∨ (a i) % 5 = 4 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1)
      ·
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
      ·
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
      ·
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
      ·
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
      ·
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod]
    omega
  have h2 : (∑ i : Fin n, (a i) ^ 5) % 30 = (∑ i : Fin n, (a i)) % 30 := by
    simp [Finset.sum_int_mod, h1]
    <;> omega
  omega