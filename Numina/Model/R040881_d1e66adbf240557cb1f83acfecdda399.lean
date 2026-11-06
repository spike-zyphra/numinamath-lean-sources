import Mathlib

theorem number_theory_103621 :
  {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ Nat.factorial x + 3 = y ^ 2} =
  {(1, 2), (3, 3)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- First: check if (x,y) satisfy the equation.
    rintro ⟨hx, hy, heq⟩
    by_cases h : x < 4
    · -- x < 4
      interval_cases x <;> try { 
        norm_num [Nat.factorial] at heq 
        all_goals 
          have : y ≤ 7 := by nlinarith 
          interval_cases y <;> omega 
      }
    · -- x >= 4
      have h1 : x ≥ 4 := by omega
      -- Then y^2 = x! +3.
      -- x! is divisible by 4 [since 4 divides x! for x >= 4]. Then x! +3 ≡3 mod4.
      -- But squares are 0 or 1 mod4. Contradiction.
      -- Now we need modulo in Lean.
      have h3 : (Nat.factorial x) % 4 = 0 := by
        have h4 : x ≥ 4 := h1
        have h5 : 4 ∣ Nat.factorial x := by
          apply Nat.dvd_factorial 
          all_goals 
            omega 
        omega 
      have h4 : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by 
        omega 
      have h5 : (y ^ 2) % 4 = 0 ∨ (y ^ 2) % 4 = 1 := by 
        rcases h4 with (h | h | h | h) <;> simp [Nat.pow_mod, h, Nat.mul_mod] 
      -- From heq. 
      have h6 : (Nat.factorial x + 3) % 4 = 3 := by
        omega
      have h7 : (Nat.factorial x + 3) % 4 = (y ^ 2) % 4 := by 
        omega 
      omega 
  · -- Show that (1, 2) and (3, 3) satisfy the equation.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Show that (1, 2) is in the left side.
      constructor
      · norm_num
      constructor
      · norm_num
      all_goals
        norm_num [Nat.factorial]
    · -- Show that (3, 3) is in the left side.
      constructor
      · norm_num
      constructor
      · norm_num
      all_goals 
        norm_num [Nat.factorial]