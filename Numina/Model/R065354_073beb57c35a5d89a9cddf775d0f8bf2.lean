import Mathlib

theorem number_theory_209195 {A B C : ℕ} (h₀ : A ≠ 0) (h₁ : A ≤ 9) (h₂ : B ≤ 9) (h₃ : C ≤ 9)
    (h₄ : 100 * A + 10 * B + C % (10 * A + B) = 0) (h₅ : 100 * A + 10 * B + C % (10 * B + C) = 0) :
    A = 9 ∧ B = 9 ∧ C = 0 := by
  have h6 : C = 0 := by
    -- We analyze the constraint h₄
    -- From h₄, we have 100A + 10B + C ≡ 0 (mod (10A + B))
    -- But 100A + 10B + C ≡ C (mod (10A + B))
    -- So C must be divisible by (10A + B). But 10A + B ≥ 10, and C ≤ 9. Therefore, C must be 0
    omega
  have h7 : A = 9 := by
    -- Given C = 0, the number becomes 100A + 10B. To maximize, we need the largest 100A + 10B
    -- which is 990, which is 990, so 100A + 10B = 990
    -- Solving, we get 10A + B = 99, so A = 9, B = 9
    omega
  have h8 : B = 9 := by
    -- Solving 10A + B = 99, we need B = 9
    omega
  exact ⟨h7, h8, h6⟩