import Mathlib

theorem algebra_106918 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (1/2)^x + (2/3)^x + (5/6)^x) :
  {x : ℤ | x ≥ 0 ∧ ∃ n : ℤ, f x = n}.ncard = 3 := by
  have h1 : {x : ℤ | x ≥ 0 ∧ ∃ n : ℤ, f x = n} = {0, 1, 3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- If x is a non-negative integer such that f x is integer, then x ∈ {0, 1, 3}
      rintro ⟨hx, n, hn⟩
      have hx2 : x ≥ (0 : ℤ) := hx
      by_cases h9 : x > 3
      · -- Assume x > 3, prove contradiction
        have h10 : x ≥ (4 : ℤ) := by omega
        have h100 : (1 / 2 : ℝ) ^ (x : ℝ) + (2 / 3 : ℝ) ^ (x : ℝ) + (5 / 6 : ℝ) ^ (x : ℝ) < (1 : ℝ) := by
          have h13 : x ≥ (4 : ℤ) := h10
          have h14 : (x : ℝ) ≥ (4 : ℝ) := by exact_mod_cast show (x : ℤ) ≥ (4 : ℤ) by omega
          have h15 : (1 / 2 : ℝ) ^ (x : ℝ) ≤ (1 / 2 : ℝ) ^ (4 : ℝ) := by
            have h22 : (1 / 2 : ℝ) < 1 := by norm_num
            have h33 : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast show (4 : ℤ) ≤ (x : ℤ) by omega
            have h44 : (1 / 2 : ℝ) ^ (x : ℝ) ≤ (1 / 2 : ℝ) ^ (4 : ℝ) := by
              apply Real.rpow_le_rpow_of_exponent_ge
              all_goals
                try linarith
            exact h44
          have h17 : (2 / 3 : ℝ) ^ (x : ℝ) ≤ (2 / 3 : ℝ) ^ (4 : ℝ) := by
            have h22 : (2 / 3 : ℝ) < 1 := by norm_num
            have h33 : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast show (4 : ℤ) ≤ (x : ℤ) by omega
            have h44 : (2 / 3 : ℝ) ^ (x : ℝ) ≤ (2 / 3 : ℝ) ^ (4 : ℝ) := by
              apply Real.rpow_le_rpow_of_exponent_ge
              all_goals
                try linarith
            exact h44
          have h19 : (5 / 6 : ℝ) ^ (x : ℝ) ≤ (5 / 6 : ℝ) ^ (4 : ℝ) := by
            have h22 : (5 / 6 : ℝ) < 1 := by norm_num
            have h33 : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast show (4 : ℤ) ≤ (x : ℤ) by omega
            have h44 : (5 / 6 : ℝ) ^ (x : ℝ) ≤ (5 / 6 : ℝ) ^ (4 : ℝ) := by
              apply Real.rpow_le_rpow_of_exponent_ge
              all_goals
                try linarith
            exact h44
          have h24 : (1 / 2 : ℝ) ^ (4 : ℝ) + (2 / 3 : ℝ) ^ (4 : ℝ) + (5 / 6 : ℝ) ^ (4 : ℝ) < (1 : ℝ) := by
            norm_num
          have h16 : (1 / 2 : ℝ) ^ (x : ℝ) + (2 / 3 : ℝ) ^ (x : ℝ) + (5 / 6 : ℝ) ^ (x : ℝ) ≤ (1 / 2 : ℝ) ^ (4 : ℝ) + (2 / 3 : ℝ) ^ (4 : ℝ) + (5 / 6 : ℝ) ^ (4 : ℝ) := by
            nlinarith [h15, h17, h19]
          linarith
        have h150 : f (x : ℝ) = (1 / 2 : ℝ) ^ (x : ℝ) + (2 / 3 : ℝ) ^ (x : ℝ) + (5 / 6 : ℝ) ^ (x : ℝ) := by
          specialize h₀ (x : ℝ)
          simpa using h₀
        have h151 : f (x : ℝ) < 1 := by
          linarith [h100, h150]
        have h11 : (↑n : ℝ) < 1 := by
          have h19 : f (x : ℝ) = (↑n : ℝ) := by exact_mod_cast hn
          nlinarith
        have h181 : n < 1 := by
          by_contra h22
          push_neg at h22
          have h23 : n ≥ 1 := by omega
          have h322 : (↑n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast show (n : ℤ) ≥ (1 : ℤ) by omega
          nlinarith
        have h232 : n ≤ 0 := by omega
        have h231 : (↑n : ℝ) > (0 : ℝ) := by
          have h191 : (↑n : ℝ) = (1 / 2 : ℝ) ^ (x : ℝ) + (2 / 3 : ℝ) ^ (x : ℝ) + (5 / 6 : ℝ) ^ (x : ℝ) := by
            have h194 : f (x : ℝ) = (↑n : ℝ) := by exact_mod_cast hn
            have h163 : f (x : ℝ) = (1 / 2 : ℝ) ^ (x : ℝ) + (2 / 3 : ℝ) ^ (x : ℝ) + (5 / 6 : ℝ) ^ (x : ℝ) := by
              specialize h₀ (x : ℝ)
              simpa using h₀
            linarith [h194, h163]
          have h163 : (1 / 2 : ℝ) ^ (x : ℝ) + (2 / 3 : ℝ) ^ (x : ℝ) + (5 / 6 : ℝ) ^ (x : ℝ) > (0 : ℝ) := by
            have h16a : (1 / 2 : ℝ) ^ (x : ℝ) > 0 := by positivity
            have h17a : (2 / 3 : ℝ) ^ (x : ℝ) > 0 := by positivity
            have h18a : (5 / 6 : ℝ) ^ (x : ℝ) > 0 := by positivity
            linarith
          nlinarith
        have h441 : (↑n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast show (n : ℤ) ≤ (0 : ℤ) by omega
        nlinarith
      push_neg at h9
      have h8a : x ≤ (3 : ℤ) := by omega
      have h9a : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
      rcases h9a with (r | r | r | r)
      · -- x = 0
        rw [show x = (0 : ℤ) by omega]
        tauto
      · -- x = 1
        rw [show x = (1 : ℤ) by omega]
        tauto
      · -- x = 2
        rw [show x = (2 : ℤ) by omega] at hn
        -- x = 2, contradiction
        have h12 : f (2 : ℝ) = (25 / 18 : ℝ) := by
          rw [h₀]
          norm_num
        norm_num [h12] at hn
        have h13 : (25 / 18 : ℝ) = (↑n : ℝ) := by
          linarith [hn]
        -- show 25/18 is not integer
        have h19 : (25 : ℤ) = 18 * (n : ℤ) := by
          have h14 : (25 : ℝ) = 18 * (↑n : ℝ) := by
            have h11 : (25 / 18 : ℝ) = (↑n : ℝ) := h13
            field_simp at h11 ⊢
            nlinarith
          exact_mod_cast h14
        omega
      · -- x = 3
        rw [show x = (3 : ℤ) by omega]
        tauto
    · -- If x ∈ {0, 1, 3}, then x is a non-negative integer with f x integer
      rintro (rfl | rfl | rfl)
      · -- x = 0
        constructor
        · norm_num
        · use 3
          norm_num [h₀]
      · -- x = 1
        constructor
        · norm_num
        · use 2
          norm_num [h₀]
      · -- x = 3
        constructor
        · norm_num
        · use 1
          norm_num [h₀]
  rw [h1]
  rw [Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals
    norm_num