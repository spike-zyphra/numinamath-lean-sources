import Mathlib

theorem number_theory_223608 (n : ℕ) (h₀ : n < 1000) :
    7 ∣ (523000 + n) ∧ 8 ∣ (523000 + n) ∧ 9 ∣ (523000 + n) ↔
    (523000 + n = 523152 ∨ 523000 + n = 523656) := by
  constructor
  · -- Forward direction: if the number is divisible by 7, 8, 9, it equals 523152 or 523656
    intro h
    rcases h with ⟨h7, h8, h9⟩
    have h₁ : n < 1000 := h₀
    have h2 : (523000 + n) % 7 = 0 := by
      omega
    have h3 : (523000 + n) % 8 = 0 := by
      omega
    have h4 : (523000 + n) % 9 = 0 := by
      omega
    have : n = 152 ∨ n = 656 := by
      interval_cases n <;> omega
    rcases this with (r₁ | r₂)
    · -- Case where n = 152, so 523000 + n = 523152
      have h₃ : 523000 + n = 523152 := by
        omega
      left
      exact h₃
    · -- Case where n = 656, so 523000 + n = 523656
      have h₄ : 523000 + n = 523656 := by
        omega
      right
      exact h₄
  · -- Backward direction: if it equals 523152 or 523656, then it's divisible by 7, 8, 9
    rintro (h | h)
    · -- Case where 523000 + n = 523152
      have h₂ : n = 152 := by
        omega
      constructor
      · -- Check divisibility by 7
        norm_num [show 523000 + n = 523152 by omega]
      constructor
      · -- Check divisibility by 8
        norm_num [show 523000 + n = 523152 by omega]
      · -- Check divisibility by 9
        norm_num [show 523000 + n = 523152 by omega]
    · -- Case where 523000 + n = 523656
      have h₂ : n = 656 := by
        omega
      constructor
      · -- Check divisibility by 7
        norm_num [show 523000 + n = 523656 by omega]
      constructor
      · -- Check divisibility by 8
        norm_num [show 523000 + n = 523656 by omega]
      · -- Check divisibility by 9
        norm_num [show 523000 + n = 523656 by omega]