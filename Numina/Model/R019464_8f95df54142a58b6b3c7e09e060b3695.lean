import Mathlib

theorem number_theory_157793 {p : ℕ → ℕ} (hp : ∀ n, Nat.Prime (p n))
    (hpn : ∀ n, Nat.Prime (p n + 100)) :
    ∀ n, p n > 3 → ¬∃ m, Nat.Prime m ∧ m = p n + 100 ∧ Nat.Prime (m - 2) := by 
  intro n h1
  rintro ⟨m, hm1, hm2, hm3⟩
  have h2 : m = p n + 100 := by linarith
  have h3 : m - 2 = p n + 98 := by 
    rw [h2]
    omega
  have hp1 : p n % 3 = 1 ∨ p n % 3 = 2 := by
    have h1' : Nat.Prime (p n) := hp n
    by_contra h
    push_neg at h
    have h2 : p n % 3 = 0 := by 
      omega
    have h3 : p n > 3 := h1
    have h4 : ¬ Nat.Prime (p n) := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p n by omega)
      all_goals omega
    tauto
  have hp2 : Nat.Prime m := by 
    tauto
  have hp3 : Nat.Prime (m - 2) := hm3
  rw [h3] at hp3
  rw [h2] at hp2
  rcases hp1 with (h4 | h4)
  · -- Assume p n ≡ 1 (mod 3)
    have h6 : (p n + 98) % 3 = 0 := by
      omega
    have h7 : (p n + 98) > 3 := by 
      omega
    have h8 : ¬ Nat.Prime (p n + 98) := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p n + 98) by omega)
      all_goals omega
    tauto
  · -- Assume p n ≡ 2 (mod 3)
    have h6 : (p n + 100) % 3 = 0 := by
      omega
    have h7 : (p n + 100) > 3 := by 
      omega
    have h8 : ¬ Nat.Prime (p n + 100) := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p n + 100) by omega)
      all_goals omega
    tauto