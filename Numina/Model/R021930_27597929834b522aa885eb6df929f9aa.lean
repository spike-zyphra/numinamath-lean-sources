import Mathlib

theorem algebra_322251 (f : ℕ → ℕ) (hf : ∀ x, f x = x ^ 2)
    (h : ∀ y, ∃ x, f x = y ∧ 1 ≤ y ∧ y ≤ 2012 ^ 2) :
    Set.ncard {f' : ℕ → ℕ | (∀ x, f' x = x ^ 2) ∧
      (∀ y, ∃ x, f' x = y ∧ 1 ≤ y ∧ y ≤ 2012 ^ 2)} = 3 ^ 2012 := by
  have h1 := h 3
  rcases h1 with ⟨x, hfx, h1le, hle⟩
  have h2 : f x = x ^ 2 := hf x
  rw [h2] at hfx
  -- x^2 = 3, which is impossible in ℕ.
  have h3 : x ≤ 2 := by nlinarith
  interval_cases x <;> omega