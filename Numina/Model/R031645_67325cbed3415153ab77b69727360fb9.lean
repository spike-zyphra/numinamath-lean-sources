import Mathlib

theorem number_theory_107983 (x y : ℕ) (hx : x > 0) (hy : y > 0) :
    x^2 - Nat.factorial y = 2019 ↔ (x = 45 ∧ y = 3) := by
  constructor
  · -- Forward direction: If x^2 - y! = 2019, then (x, y) = (45, 3)
    intro h
    have h1 : x ^ 2 = 2019 + Nat.factorial y := by 
      have h2 : x ^ 2 ≥ Nat.factorial y := by
        by_contra h3
        push_neg at h3
        have h4 : x ^ 2 - Nat.factorial y = 0 := by
          rw [Nat.sub_eq_zero_iff_le]
          linarith
        omega
      omega
    by_cases h2 : y ≤ 4
    · -- y <= 4, so y can be 1, 2, 3, 4
      interval_cases y <;> try { 
        norm_num [Nat.factorial] at h1
        all_goals
          have : x ≤ 50 := by nlinarith
          interval_cases x <;> omega
      }
    · -- y > 4
      have h3 : y ≥ 5 := by
        omega
      have h4 : Nat.factorial y % 4 = 0 := by
        have h4 : 4 ∣ Nat.factorial y := by
          apply Nat.dvd_factorial
          all_goals 
            omega
        omega
      have h5 : x ^ 2 % 4 = 3 := by
        have h6 : x ^ 2 = 2019 + Nat.factorial y := h1
        have h7 : x ^ 2 % 4 = (2019 + Nat.factorial y) % 4 := by 
          rw [h6]
        omega
      have h6 : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
        have : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by 
          omega
        rcases this with (h | h | h | h) <;> simp [pow_two, Nat.add_mod, Nat.mul_mod, h] 
      omega
  · -- Backward direction: If (x, y) = (45, 3), then x^2 - y! = 2019
    rintro ⟨rfl, rfl⟩
    norm_num [Nat.factorial]