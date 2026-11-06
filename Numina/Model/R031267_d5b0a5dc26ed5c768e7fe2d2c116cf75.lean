import Mathlib

theorem number_theory_604818 (a b c : ℤ) (p : ℕ) (hp : p.Prime) :
(73 : ℤ) * p ^ 2 + 6 = 9 * a ^ 2 + 17 * b ^ 2 + 17 * c ^ 2 ↔ (a = 1 ∨ a = -1) ∧ p = 2 ∧
((b = 1 ∧ c = 4) ∨ (b = -1 ∧ c = 4) ∨ (b = 1 ∧ c = -4) ∨ (b = -1 ∧ c = -4) ∨
(b = 4 ∧ c = 1) ∨ (b = -4 ∧ c = 1) ∨ (b = 4 ∧ c = -1) ∨ (b = -4 ∧ c = -1)) := by
  constructor
  · -- Assume LHS, prove RHS
    rintro h
    have h1 : p = 2 := by
      by_cases h2 : p > 2
      · -- Assume p > 2.
        have h3 : p % 2 = 1 := by
          by_contra h4
          push_neg at h4
          have h5 : p % 2 = 0 := by omega
          have h6 : p > 2 := h2
          have h7 : ¬p.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
          contradiction
        have h8 : (p : ℤ) % 8 = 1 ∨ (p : ℤ) % 8 = 3 ∨ (p : ℤ) % 8 = 5 ∨ (p : ℤ) % 8 = 7 := by 
          omega
        have h9 : ((p : ℤ) ^ 2 : ℤ) % 8 = 1 := by
          rcases h8 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
        have h10 : (9 * a ^ 2 + 17 * b ^ 2 + 17 * c ^ 2 : ℤ) % 8 = 7 := by 
          omega
        have h14 : (9 * a ^ 2 + 17 * b ^ 2 + 17 * c ^ 2 : ℤ) % 8 = (a^2 + b^2 + c^2) % 8 := by 
          simp [Int.add_emod, Int.mul_emod, Int.sub_emod]
        rw [h14] at h10
        have h13 : (a ^ 2 + b ^ 2 + c ^ 2 : ℤ) % 8 ≠ 7 := by
          have h13a : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by 
            have h13a : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by
              omega
            rcases h13a with (h | h | h | h | h | h | h | h) <;> simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
          have h14b : b ^ 2 % 8 = 0 ∨ b ^ 2 % 8 = 1 ∨ b ^ 2 % 8 = 4 := by 
            have h13b : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by
              omega
            rcases h13b with (h | h | h | h | h | h | h | h) <;> simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
          have h14c : c ^ 2 % 8 = 0 ∨ c ^ 2 % 8 = 1 ∨ c ^ 2 % 8 = 4 := by 
            have h13c : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by
              omega
            rcases h13c with (h | h | h | h | h | h | h | h) <;> simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
          omega
        omega
      · -- Assume p ≤ 2.
        have h3 : p ≤ 2 := by omega
        interval_cases p <;> norm_num at hp ⊢ <;> try { trivial }
    have h2 : p = 2 := h1
    rw [show (p : ℕ) = 2 by omega] at h
    -- So now we can rewrite p = 2 in the equation, so we get:
    -- 73 \cdot 2^2 + 6 = 9a^2 + 17b^2 + 17c^2, which is 298 = 9a^2 + 17b^2 + 17c^2
    have h3 : 9 * a ^ 2 + 17 * b ^ 2 + 17 * c ^ 2 = 298 := by
      norm_num at h ⊢
      nlinarith
    -- Let's bound the variables.
    have ha1 : a ≤ 5 := by nlinarith [sq_nonneg (a : ℤ), sq_nonneg (b : ℤ), sq_nonneg (c : ℤ)]
    have ha2 : a ≥ -5 := by nlinarith [sq_nonneg (a : ℤ), sq_nonneg (b : ℤ), sq_nonneg (c : ℤ)]
    have hb1 : b ≤ 4 := by nlinarith [sq_nonneg (a : ℤ), sq_nonneg (b : ℤ), sq_nonneg (c : ℤ)]
    have hb2 : b ≥ -4 := by nlinarith [sq_nonneg (a : ℤ), sq_nonneg (b : ℤ), sq_nonneg (c : ℤ)]
    have hc1 : c ≤ 4 := by nlinarith [sq_nonneg (a : ℤ), sq_nonneg (b : ℤ), sq_nonneg (c : ℤ)]
    have hc2 : c ≥ -4 := by nlinarith [sq_nonneg (a : ℤ), sq_nonneg (b : ℤ), sq_nonneg (c : ℤ)]
    -- Now, we need to check all possible quadruples (a, b, c) where a is from -5 to 5, b and c from -4 to 4.
    have h10 : (a = 1 ∨ a = -1) := by 
      interval_cases a <;> try { 
        omega
      }
    have hp2 : p = 2 := by omega
    constructor
    · tauto
    constructor
    · tauto
    · -- Now need to prove about the quadruples
      interval_cases a <;> try { 
        omega
      } <;> try { 
        interval_cases b <;> try { 
          omega
        } <;> try { 
          interval_cases c <;> omega
        }
      }
  · -- Assume RHS, prove LHS
    rintro ⟨ha, hp2, h1⟩
    have hp2' : p = 2 := by 
      tauto
    rw [show (p : ℕ) = 2 by omega]
    rcases ha with (rfl | rfl)
    · -- a = 1
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1)
      · -- (b = 1 ∧ c = 4)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num
      · -- (b = -1 ∧ c = 4)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num
      · -- (b = 1 ∧ c = -4)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num
      · -- (b = -1 ∧ c = -4)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num
      · -- (b = 4 ∧ c = 1)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num
      · -- (b = -4 ∧ c = 1)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num
      · -- (b = 4 ∧ c = -1)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num
      · -- (b = -4 ∧ c = -1)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num
    · -- a = -1
      rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1)
      · -- (b = 1 ∧ c = 4)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num
      · -- (b = -1 ∧ c = 4)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num
      · -- (b = 1 ∧ c = -4)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num
      · -- (b = -1 ∧ c = -4)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num
      · -- (b = 4 ∧ c = 1)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num
      · -- (b = -4 ∧ c = 1)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num
      · -- (b = 4 ∧ c = -1)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num
      · -- (b = -4 ∧ c = -1)
        rcases h1 with ⟨rfl, rfl⟩
        all_goals
          norm_num