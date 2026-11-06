import Mathlib

theorem number_theory_176836 {p1 p2 : ℕ} (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hpn : p1 > p2) (h : p1 - p2 = 2) (h2 : p2 > 3) :
    12 ∣ p1 + p2 := by 
  have h1 : p1 = p2 + 2 := by 
    omega
  have h3 : p1 + p2 = 2 * p2 + 2 := by 
    rw [h1]
    all_goals ring
  have h4 : p2 % 3 = 1 ∨ p2 % 3 = 2 := by
    by_contra h6
    push_neg at h6
    have h7 : p2 % 3 = 0 := by omega
    have h5 : p2 > 3 := by linarith
    have h8 : ¬(p2.Prime) := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p2 by omega)
      all_goals omega
    tauto
  have h6 : p2 % 2 = 1 := by
    by_contra h9
    push_neg at h9
    have h2' : p2 % 2 = 0 := by omega
    have h8 : p2 > 3 := by linarith
    have h7 : ¬(p2.Prime) := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p2 by omega)
      all_goals omega
    tauto
  have h3' : (2 * p2 + 2) % 4 = 0 := by
    have : p2 % 2 = 1 := h6
    omega
  by_cases h9 : p2 % 3 = 1
  · -- Assume p2 ≡ 1 (mod 3)
    have h10 : p1 % 3 = 0 := by
      have h1 : p1 = p2 + 2 := by 
        omega
      omega
    have h3 : p1 ≠ 3 := by
      omega
    have h8 : ¬(p1.Prime) := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p1 by omega)
      all_goals
      omega
    contradiction
  · -- Assume p2 ≡ 2 (mod 3)
    have h8' : p2 % 3 = 2 := by 
      omega
    have h9 : (2 * p2 + 2) % 3 = 0 := by 
      omega
    omega