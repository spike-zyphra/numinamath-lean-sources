import Mathlib

theorem number_theory_228874 (a b c : ℤ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : 0 < c)
    (h₂ : a ≠ b) (h₃ : a ≠ c) (h₄ : b ≠ c) :
    10 ∣ a^3 * b - a * b^3 ∨ 10 ∣ b^3 * c - b * c^3 ∨ 10 ∣ c^3 * a - c * a^3 := by
  by_contra h
  push_neg at h 
  have h1 : ¬ (10 ∣ a^3 * b - a * b^3) := by 
    omega
  have h2 : ¬ (10 ∣ b^3 * c - b * c^3) := by 
    omega 
  have h3 : ¬ (10 ∣ c^3 * a - c * a^3) := by 
    omega 
  -- Prove they must be divisible by 2.
  have h5 : (a^3 * b - a * b^3) % 2 = 0 := by 
    have h5a : a % 2 = 0 ∨ a % 2 = 1 := by omega 
    have h5b : b % 2 = 0 ∨ b % 2 = 1 := by omega 
    rcases h5a with (h5a | h5a) <;> rcases h5b with (h5b | h5b)
    all_goals 
      simp [h5a, h5b, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  -- Prove they must be divisible by 2.
  have h6 : (b^3 * c - b * c^3) % 2 = 0 := by 
    have h6b : b % 2 = 0 ∨ b % 2 = 1 := by omega 
    have h6c : c % 2 = 0 ∨ c % 2 = 1 := by omega 
    rcases h6b with (h6b | h6b) <;> rcases h6c with (h6c | h6c)
    all_goals 
      simp [h6b, h6c, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  -- Prove they must be divisible by 2.
  have h7 : (c^3 * a - c * a^3) % 2 = 0 := by 
    have h7c : c % 2 = 0 ∨ c % 2 = 1 := by omega 
    have h7a : a % 2 = 0 ∨ a % 2 = 1 := by omega 
    rcases h7c with (h7c | h7c) <;> rcases h7a with (h7a | h7a)
    all_goals 
      simp [h7c, h7a, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  -- deriving implication with modulo 5
  -- Assume none of the expressions is divisible by 5
  have h5a : (a^3 * b - a * b^3) % 5 = 1 ∨ (a^3 * b - a * b^3) % 5 = 2 ∨ (a^3 * b - a * b^3) % 5 = 3 ∨ (a^3 * b - a * b^3) % 5 = 4 := by 
    omega
  -- Assume none of the expressions is divisible by 5
  have h5b : (b^3 * c - b * c^3) % 5 = 1 ∨ (b^3 * c - b * c^3) % 5 = 2 ∨ (b^3 * c - b * c^3) % 5 = 3 ∨ (b^3 * c - b * c^3) % 5 = 4 := by 
    omega
  -- Assume none of the expressions is divisible by 5
  have h5c : (c^3 * a - c * a^3) % 5 = 1 ∨ (c^3 * a - c * a^3) % 5 = 2 ∨ (c^3 * a - c * a^3) % 5 = 3 ∨ (c^3 * a - c * a^3) % 5 = 4 := by 
    omega
  -- Now call exhaustive backtrack
  have h5d : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
    omega
  have h5e : b % 5 = 0 ∨ b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by 
    omega 
  have h5f : c % 5 = 0 ∨ c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by 
    omega 
  rcases h5d with (h5d | h5d | h5d | h5d | h5d) <;> rcases h5e with (h5e | h5e | h5e | h5e | h5e) <;> rcases h5f with (h5f | h5f | h5f | h5f | h5f) <;> 
    norm_num [Int.add_emod, Int.mul_emod, Int.sub_emod, pow_succ, h5d, h5e, h5f] at h5a h5b h5c