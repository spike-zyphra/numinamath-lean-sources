import Mathlib

theorem number_theory_219131 (n m : ℕ) (h₀ : n < 100000) (h₁ : m < 100000)
    (h₂ : n + m = 111111) (h₃ : ∃ a b, a ≠ b ∧ n = 10000 * a + 1000 * b + 100 * (10 - a) + 10 * (10 - b) + (10 - (10 - a)) ∧
    m = 10000 * b + 1000 * (10 - a) + 100 * (10 - b) + 10 * (10 - (10 - a)) + (10 - (10 - b))) :
    0 ∈ Nat.digits 10 n ∨ 0 ∈ Nat.digits 10 m := by
  rcases h₃ with ⟨a, b, hab, hn, hm⟩
  omega
  all_goals try { norm_num [hn, hm] at * <;> omega }
  all_goals try { tauto }