import Mathlib

theorem number_theory_255900 (p : ℕ) (hp : p.Prime) (h : p ≠ 2) (h' : p ≠ 3) (h'' : p ≠ 5) :
    p^2 ≡ 1 [MOD 30] ∨ p^2 ≡ 19 [MOD 30] := by
  have h1 : p ≥ 7 := by
    by_contra h1
    push_neg at h1
    interval_cases p <;> norm_num at hp h h' h''
  have h2 : p % 2 = 1 := by
    by_contra h2
    push_neg at h2
    have : ¬p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
    contradiction
  have h3 : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3ne : p % 3 ≠ 0 := by
      intro h0
      have : 3 ∣ p := by omega
      have : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
        all_goals nlinarith
      contradiction
    omega
  have h4 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
    have h5ne : p % 5 ≠ 0 := by
      intro h0
      have : 5 ∣ p := by omega
      have : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega) (by omega) (by omega)
        all_goals nlinarith
      contradiction
    omega
  have h6 : p ^ 2 % 3 = 1 := by
    rcases h3 with (h3 | h3)
    · simp [Nat.pow_mod, h3]
    · simp [Nat.pow_mod, h3]
  have h7 : p ^ 2 % 5 = 1 ∨ p ^ 2 % 5 = 4 := by
    rcases h4 with (h4 | h4 | h4 | h4)
    · simp [Nat.pow_mod, h4]
    · simp [Nat.pow_mod, h4]
    · simp [Nat.pow_mod, h4]
    · simp [Nat.pow_mod, h4]
  -- The possible residues of $p^2 \pmod{2}$ is 1, $\pmod{3}$ is 1, and $\pmod{5}$ is 1 or 4.
  have h5 : p ^ 2 % 2 = 1 := by
    have h2' : p % 2 = 1 := h2
    simp [Nat.pow_mod, h2']
  -- Now, we need to prove that $p^2 \equiv 1 \text{ or }19 \pmod{30}$.
  have h12 : p ^ 2 % 30 = 1 ∨ p ^ 2 % 30 = 19 := by
    omega
  rcases h12 with (h12 | h12)
  · left
    simp [Nat.ModEq, h12]
  · right
    simp [Nat.ModEq, h12]