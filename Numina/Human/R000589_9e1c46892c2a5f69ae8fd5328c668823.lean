import Mathlib

theorem algebra_12970 (a b c d : ℝ) (ha : a ≠ 0) 
    (hroots : (1 : ℝ) ∈ {x | a * x ^ 3 + b * x ^ 2 + c * x + d = 0} ∧
              (2 : ℝ) ∈ {x | a * x ^ 3 + b * x ^ 2 + c * x + d = 0} ∧ 
              (3 : ℝ) ∈ {x | a * x ^ 3 + b * x ^ 2 + c * x + d = 0}
    ) : c / d = -11 / 6 := by
  rcases hroots with ⟨h1, h2, h3⟩
  have h1' : a * 1 ^ 3 + b * 1 ^ 2 + c * 1 + d = 0 := h1
  have h2' : a * 2 ^ 3 + b * 2 ^ 2 + c * 2 + d = 0 := h2
  have h3' : a * 3 ^ 3 + b * 3 ^ 2 + c * 3 + d = 0 := h3
  have hd : d ≠ 0 := by
    intro h
    have : a = 0 := by linarith
    contradiction
  have : c / d = -11 / 6 := by
    field_simp [hd]
    linarith
  exact this