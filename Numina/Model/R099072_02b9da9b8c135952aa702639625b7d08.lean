import Mathlib

theorem number_theory_65924 :
    ¬∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (∃ m n p : ℕ, m^2 = a^2 * b * c + 2 ∧ n^2 = b^2 * c * a + 2 ∧ p^2 = c^2 * a * b + 2) := by
  rintro ⟨a, b, c, ha, hb, hc, ⟨m, n, p, hm, hn, hp⟩⟩
  have h1 : m^2 % 8 = 0 ∨ m^2 % 8 = 1 ∨ m^2 % 8 = 4 := by
    have h : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by
      omega
    rcases h with (h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
  have h2 : n^2 % 8 = 0 ∨ n^2 % 8 = 1 ∨ n^2 % 8 = 4 := by
    have h : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
      omega
    rcases h with (h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
  have h3 : p^2 % 8 = 0 ∨ p^2 % 8 = 1 ∨ p^2 % 8 = 4 := by
    have h : p % 8 = 0 ∨ p % 8 = 1 ∨ p % 8 = 2 ∨ p % 8 = 3 ∨ p % 8 = 4 ∨ p % 8 = 5 ∨ p % 8 = 6 ∨ p % 8 = 7 := by
      omega
    rcases h with (h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
  have h4 : (a^2 * b * c + 2) % 8 = m^2 % 8 := by omega
  have h5 : (b^2 * c * a + 2) % 8 = n^2 % 8 := by omega
  have h6 : (c^2 * a * b + 2) % 8 = p^2 % 8 := by omega
  have h7 : (a^2 * b * c + 2) % 8 = 0 ∨ (a^2 * b * c + 2) % 8 = 1 ∨ (a^2 * b * c + 2) % 8 = 4 := by
    omega
  have h8 : (a^2 * b * c) % 8 = 6 ∨ (a^2 * b * c) % 8 = 7 ∨ (a^2 * b * c) % 8 = 2 := by
    omega
  have h9 : (b^2 * c * a + 2) % 8 = 0 ∨ (b^2 * c * a + 2) % 8 = 1 ∨ (b^2 * c * a + 2) % 8 = 4 := by
    omega
  have h10 : (b^2 * c * a) % 8 = 6 ∨ (b^2 * c * a) % 8 = 7 ∨ (b^2 * c * a) % 8 = 2 := by
    omega
  have h11 : (c^2 * a * b + 2) % 8 = 0 ∨ (c^2 * a * b + 2) % 8 = 1 ∨ (c^2 * a * b + 2) % 8 = 4 := by
    omega
  have h12 : (c^2 * a * b) % 8 = 6 ∨ (c^2 * a * b) % 8 = 7 ∨ (c^2 * a * b) % 8 = 2 := by
    omega
  have ha2 : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
    omega
  have hb2 : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
    omega
  have hc2 : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by
    omega
  rcases ha2 with (h | h | h | h | h | h | h | h) <;> rcases hb2 with (h' | h' | h' | h' | h' | h' | h' | h') <;> rcases hc2 with (h'' | h'' | h'' | h'' | h'' | h'' | h'' | h'') <;> simp [Nat.mul_mod, Nat.pow_mod, h, h', h''] at h8 h10 h12 ⊢ <;> omega