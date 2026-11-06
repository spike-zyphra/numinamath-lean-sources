import Mathlib

theorem number_theory_88742 (k : ℕ) (hk : 0 < k) :
    ∃ x y : ℤ, ¬(3 ∣ x) ∧ ¬(3 ∣ y) ∧ x^2 + 2 * y^2 = 3^k := by
  have h1 : ∀ (k : ℕ), k ≥ 1 → ∃ x y : ℤ, ¬(3 ∣ x) ∧ ¬(3 ∣ y) ∧ x^2 + 2 * y^2 = 3^k := by
    intro k hk
    induction k with
    | zero => 
      exfalso
      omega
    | succ k ih =>
      cases k with
      | zero =>
        use 1, 1
        all_goals norm_num
      | succ k =>
        rcases ih (by linarith) with ⟨x, y, hx, hy, heq⟩
        have h3 : x % 3 = 1 ∨ x % 3 = 2 := by 
          omega
        have h4 : y % 3 = 1 ∨ y % 3 = 2 := by 
          omega
        rcases h3 with (h3 | h3)
        · -- x % 3 = 1
          rcases h4 with (h4 | h4)
          · -- y % 3 = 1
            use x - 2 * y, x + y
            constructor
            · -- Show ¬(3 ∣ (x - 2 * y))
              omega
            constructor
            · -- Show ¬(3 ∣ (x + y))
              omega
            · -- Show (x - 2 * y)^2 + 2 * (x + y)^2 = 3 ^ (k + 1 + 1)
              ring_nf at heq ⊢
              nlinarith
          · -- y % 3 = 2
            use x + 2 * y, -x + y
            constructor
            · -- Show ¬(3 ∣ (x + 2 * y))
              omega
            constructor
            · -- Show ¬(3 ∣ (-x + y))
              omega
            · -- Show (x + 2 * y)^2 + 2 * (-x + y)^2 = 3 ^ (k + 1 + 1)
              ring_nf at heq ⊢
              nlinarith
        · -- x % 3 = 2
          rcases h4 with (h4 | h4)
          · -- y % 3 = 1
            use x + 2 * y, -x + y
            constructor
            · -- Show ¬(3 ∣ (x + 2 * y))
              omega
            constructor
            · -- Show ¬(3 ∣ (-x + y))
              omega
            · -- Show (x + 2 * y)^2 + 2 * (-x + y)^2 = 3 ^ (k + 1 + 1)
              ring_nf at heq ⊢
              nlinarith
          · -- y % 3 = 2
            use x - 2 * y, x + y
            constructor
            · -- Show ¬(3 ∣ (x - 2 * y))
              omega
            constructor
            · -- Show ¬(3 ∣ (x + y))
              omega
            · -- Show (x - 2 * y)^2 + 2 * (x + y)^2 = 3 ^ (k + 1 + 1)
              ring_nf at heq ⊢
              nlinarith
  specialize h1 k (by linarith)
  simpa using h1