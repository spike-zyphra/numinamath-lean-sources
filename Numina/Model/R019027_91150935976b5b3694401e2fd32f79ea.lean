import Mathlib

def is_totally_square (n : ℕ) := ∃ k, (Nat.digits 10 n).sum = k^2

theorem number_theory_35457 :
    ∀ N, ∃ m, m > N ∧ ¬∃ a b, a ≠ 0 ∧ b ≠ 0 ∧ m = a + b ∧ is_totally_square a ∧ is_totally_square b := by
  intro N
  have h1 : ∀ N, ∃ m, m > N ∧ m % 9 = 3 := by 
    intro N
    use (9 * (N + 1) + 3)
    constructor
    · -- Show that m > N
      omega 
    · -- Show that m % 9 = 3
      omega
  rcases h1 N with ⟨m, hm1, hm2⟩
  use m 
  constructor
  · -- Show that m > N
    exact hm1
  · -- Show that ¬∃ a b, a ≠ 0 ∧ b ≠ 0 ∧ m = a + b ∧ is_totally_square a ∧ is_totally_square b
    rintro ⟨a, b, ha, hb, hsum, h1, h2⟩
    have h3 : m % 9 = 3 := hm2
    have h8 : m = a + b := hsum
    rcases h1 with ⟨k, hk⟩
    rcases h2 with ⟨l, hl⟩
    have h9 : (Nat.digits 10 a).sum = k ^ 2 := by
      simpa using hk
    have h10 : (Nat.digits 10 b).sum = l ^ 2 := by
      simpa using hl
    have h12 : a % 9 = k ^ 2 % 9 := by
      have h13 : a % 9 = (Nat.digits 10 a).sum % 9 := by
        rw [Nat.modEq_nine_digits_sum (a)]
        all_goals omega
      have h14 : (Nat.digits 10 a).sum = k ^ 2 := by 
        simpa using hk
      rw [h14] at h13
      omega
    have h14 : b % 9 = l ^ 2 % 9 := by
      have h15 : b % 9 = (Nat.digits 10 b).sum % 9 := by
        rw [Nat.modEq_nine_digits_sum (b)]
        all_goals omega
      have h16 : (Nat.digits 10 b).sum = l ^ 2 := by 
        simpa using hl
      rw [h16] at h15
      omega
    have h11 : k ^ 2 % 9 = 0 ∨ k ^ 2 % 9 = 1 ∨ k ^ 2 % 9 = 4 ∨ k ^ 2 % 9 = 7 := by
      have h12 : k % 9 = 0 ∨ k % 9 = 1 ∨ k % 9 = 2 ∨ k % 9 = 3 ∨ k % 9 = 4 ∨ k % 9 = 5 ∨ k % 9 = 6 ∨ k % 9 = 7 ∨ k % 9 = 8 := by
        omega 
      rcases h12 with (h | h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h, Nat.add_mod, Nat.mul_mod]
    have h13 : l ^ 2 % 9 = 0 ∨ l ^ 2 % 9 = 1 ∨ l ^ 2 % 9 = 4 ∨ l ^ 2 % 9 = 7 := by
      have h14 : l % 9 = 0 ∨ l % 9 = 1 ∨ l % 9 = 2 ∨ l % 9 = 3 ∨ l % 9 = 4 ∨ l % 9 = 5 ∨ l % 9 = 6 ∨ l % 9 = 7 ∨ l % 9 = 8 := by
        omega 
      rcases h14 with (h | h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h, Nat.add_mod, Nat.mul_mod]
    omega