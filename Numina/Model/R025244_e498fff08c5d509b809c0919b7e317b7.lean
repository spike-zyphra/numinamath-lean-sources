import Mathlib

theorem number_theory_229881
    (a b c : ℕ)
    (ha : a.Prime)
    (hb : b.Prime)
    (hc : c.Prime)
    (h : ∃ p : ℕ, p.Prime ∧ a^2 + b^2 + c^2 = p) :
    a = 3 ∨ b = 3 ∨ c = 3 := by
  rcases h with ⟨p, hp, hp_eq⟩
  by_contra h
  push_neg at h
  have ha1 : a ≠ 3 := by
    omega
  have hb1 : b ≠ 3 := by
    omega
  have hc1 : c ≠ 3 := by
    omega
  have h1 : a % 3 = 1 ∨ a % 3 = 2 := by 
    have h1 : a % 3 = 1 ∨ a % 3 = 2 ∨ a % 3 = 0 := by omega
    have h2 : a % 3 ≠ 0 := by
      by_contra h2
      have h3 : a > 1 := Nat.Prime.two_le ha
      have h4 : ¬a.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ a by omega) (by omega) (by omega)
      contradiction
    tauto
  have h1' : b % 3 = 1 ∨ b % 3 = 2 := by
    have h1 : b % 3 = 1 ∨ b % 3 = 2 ∨ b % 3 = 0 := by omega
    have h2 : b % 3 ≠ 0 := by
      by_contra h2
      have h3 : b > 1 := Nat.Prime.two_le hb
      have h4 : ¬b.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ b by omega) (by omega) (by omega)
      contradiction
    tauto
  have h1'' : c % 3 = 1 ∨ c % 3 = 2 := by
    have h1 : c % 3 = 1 ∨ c % 3 = 2 ∨ c % 3 = 0 := by omega
    have h2 : c % 3 ≠ 0 := by
      by_contra h2
      have h3 : c > 1 := Nat.Prime.two_le hc
      have h4 : ¬c.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ c by omega) (by omega) (by omega)
      contradiction
    tauto
  have ha2 : a ^ 2 % 3 = 1 := by 
    rcases h1 with (h1 | h1) <;> simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
  have hb2 : b ^ 2 % 3 = 1 := by 
    rcases h1' with (h1' | h1') <;> simp [Nat.pow_mod, h1', Nat.mul_mod, Nat.add_mod]
  have hc2 : c ^ 2 % 3 = 1 := by 
    rcases h1'' with (h1'' | h1'') <;> simp [Nat.pow_mod, h1'', Nat.mul_mod, Nat.add_mod]
  -- So $p$ is a multiple of 3, and it's not 3 itself. Therefore it's possible.
  have hp2 : p % 3 = 0 := by
    omega
  have h2 : p > 3 := by
    have h1 : a ≥ 2 := Nat.Prime.two_le ha
    have h2 : b ≥ 2 := Nat.Prime.two_le hb
    have h3 : c ≥ 2 := Nat.Prime.two_le hc
    nlinarith [hp_eq, h1, h2, h3, sq_pos_of_pos (show 0 < a by linarith), sq_pos_of_pos (show 0 < b by linarith), sq_pos_of_pos (show 0 < c by linarith)]
  have hp5 : ¬p.Prime := by 
    apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega)
  contradiction