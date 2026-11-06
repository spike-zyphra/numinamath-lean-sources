import Mathlib

theorem number_theory_4232 (n : ℕ) (h : ∃ d, (n^2 + 7) = (n^2 + 1) + d ∧ (n^2 + 13) = (n^2 + 7) + d ∧ (n^2 + 19) = (n^2 + 13) + d ∧ (n^2 + 25) = (n^2 + 19) + d)
    (hn : Nat.Prime (n^2 + 1)) (hn' : Nat.Prime (n^2 + 7)) (hn'' : Nat.Prime (n^2 + 13)) (hn''' : Nat.Prime (n^2 + 19)) (hn'''' : Nat.Prime (n^2 + 25)) :
    n ≤ 2 := by

  rcases h with ⟨d, had, ⟨hdb, ⟨hdc, hdd⟩⟩⟩
  have hd : d = 6 := by omega
  -- We proceed by contradiction. Assume n > 2
  by_contra h2
  push_neg at h2
  have h20 : n ≥ 3 := by omega

  have h3 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    omega

  rcases h3 with (h | h | h | h | h)

  · -- Case n ≡0 mod5
    have h4 : (n ^ 2 + 25) % 5 = 0 := by
      have h5 : n % 5 = 0 := h
      have h6 : (n ^ 2) % 5 = 0 := by
        simp [Nat.pow_mod, h5]
      omega
    have h7 : ¬ Nat.Prime (n ^ 2 + 25) := by
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (n ^ 2 + 25) by omega)
      all_goals 
        nlinarith [h20]
    contradiction

  · -- Case n ≡1 mod5
    have h4 : (n ^ 2 + 19) % 5 = 0 := by
      have h5 : n % 5 = 1 := h
      have h6 : (n ^ 2) % 5 = 1 := by
        simp [Nat.pow_mod, h5]
      omega
    have h7 : ¬ Nat.Prime (n ^ 2 + 19) := by
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (n ^ 2 + 19) by omega)
      all_goals 
        nlinarith [h20]
    contradiction

  · -- Case n ≡2  mod5
    have h4 : (n ^ 2 + 1) % 5 = 0 := by
      have h5 : n % 5 = 2 := h
      have h6 : (n ^ 2) % 5 = 4 := by
        simp [Nat.pow_mod, h5]
      omega
    have h7 : ¬ Nat.Prime (n ^ 2 + 1) := by
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (n ^ 2 + 1)  by omega)
      all_goals 
        nlinarith [h20]
    contradiction

  · -- Case n ≡3  mod5
    have h4 : (n ^ 2 + 1) % 5 = 0 := by
      have h5 : n % 5 = 3 := h
      have h6 : (n ^ 2) % 5 = 4 := by
        simp [Nat.pow_mod, h5]
      omega
    have h7 : ¬ Nat.Prime (n ^ 2 + 1) := by
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (n ^ 2 + 1)  by omega)
      all_goals 
        nlinarith [h20]
    contradiction

  · -- Case n ≡4  mod5
    have h4 : (n ^ 2 + 19) % 5 = 0 := by
      have h5 : n % 5 = 4 := h
      have h6 : (n ^ 2) % 5 = 1 := by
        simp [Nat.pow_mod, h5]
      omega
    have h7 : ¬ Nat.Prime (n ^ 2 + 19) := by
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (n ^ 2 + 19)  by omega)
      all_goals 
        nlinarith [h20]
    contradiction