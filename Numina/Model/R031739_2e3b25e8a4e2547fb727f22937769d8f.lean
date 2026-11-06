import Mathlib

theorem number_theory_280921 (p : ℕ) (hp : p.Prime) (hne : p ≠ 1 ∧ p ≠ 2 ∧ p ≠ 3) :
    ∃ n, 6 ∣ n ∧ (p = n + 1 ∨ p = n - 1) := by 
  rcases hne with ⟨hne1, hne2, hne3⟩ 
  have h2 : p ≥ 4 := by
    by_contra h 
    push_neg at h 
    interval_cases p <;> norm_num at hp hne1 hne2 hne3 
  have h3 : p % 2 = 1 := by
    by_contra h
    push_neg at h
    have h4 : ¬p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
    contradiction
  have h4 : p % 3 = 1 ∨ p % 3 = 2 := by
    by_contra h
    push_neg at h
    have h5 : p % 3 = 0 := by 
      omega
    have h6 : 3 ∣ p := by
      omega 
    have h7 : ¬p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
    contradiction
  by_cases h5 : p % 6 = 1 
  · -- Case p ≡ 1 (mod 6)
    use p - 1 
    constructor 
    · -- Show that 6 divides n 
      have h31 : 6 ∣ (p - 1) := by 
        omega 
      exact h31 
    · -- Show that p = n + 1 or p = n - 1 
      have h32 : p = (p - 1) + 1 := by 
        omega 
      left 
      linarith 
  · -- Case p ≡ 5 (mod 6), derived from p ≡ 2 (mod 3) and p ≡ 1 (mod 2)
    have h12 : p % 6 = 5 := by
      omega
    use p + 1
    constructor 
    · -- Show that 6 divides n 
      have h31 : 6 ∣ (p + 1) := by 
        omega
      exact h31 
    · -- Show that p = n + 1 or p = n - 1 
      right 
      have h32 : p = (p + 1) - 1 := by 
        omega 
      omega