import Mathlib

theorem number_theory_74545 (n : ℤ) (h : ∃ a b, 7 * n = a ^ 2 + 3 * b ^ 2) :
    ∃ c d, n = c ^ 2 + 3 * d ^ 2 := by
  rcases h with ⟨a, b, h_eq⟩
  have eq1 : a ^ 2 + 3 * b ^ 2 = 7 * n := by
    linarith
  have h1 : (a ^ 2 + 3 * b ^ 2) % 7 = 0 := by 
    omega
  have h2 : a % 7 = 0 ∨ a % 7 = 1 ∨ a % 7 = 2 ∨ a % 7 = 3 ∨ a % 7 = 4 ∨ a % 7 = 5 ∨ a % 7 = 6 := by
    omega
  have h3 : b % 7 = 0 ∨ b % 7 = 1 ∨ b % 7 = 2 ∨ b % 7 = 3 ∨ b % 7 = 4 ∨ b % 7 = 5 ∨ b % 7 = 6 := by
    omega
  have h5 : a % 7 = (2 * (b % 7) ) % 7 ∨ a % 7 = (-2 * (b % 7) ) % 7 := by
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> 
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h2, h3] at h1 ⊢
    <;> omega
  rcases h5 with (h5 | h5)
  · -- Assume $a \equiv 2b \pmod{7}$. 
    have h5' : ∃ k, a = 2 * b + 7 * k := by
      have h4 : a % 7 = (2 * (b % 7) ) % 7 := by
        omega
      refine' ⟨(a - 2 * b) / 7, by omega⟩
    rcases h5' with ⟨k, hk⟩
    use b + 2 * k, k
    rw [hk] at eq1
    nlinarith
  · -- Assume $a \equiv -2b \pmod{7}$.
    have h5' : ∃ k, a = -2 * b + 7 * k := by 
      have h4 : a % 7 = (-2 * (b % 7) ) % 7 := by
        omega
      refine' ⟨(a + 2 * b) / 7, by omega⟩
    rcases h5' with ⟨k, hk⟩
    use b - 2 * k, k
    rw [hk] at eq1
    nlinarith