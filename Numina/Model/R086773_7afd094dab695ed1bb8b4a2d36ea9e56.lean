import Mathlib

theorem number_theory_201264 (a : Fin 99 → Fin 101 → ℕ) (ha : ∀ i j, a i j > 0)
    (h : ∀ i j, a i j = (i.1 * 101 + j.1 + 1) ^ 3) :
    200 ∣ ∑ i, ∑ j, a i j := by
  have h1 : ∀ i j, a i j = (i.1 * 101 + j.1 + 1) ^ 3 := h
  -- Unfold the sum and use the formula to compute.
  have eq1 : ∑ i, ∑ j, a i j = ∑ i : Fin 99, ∑ j : Fin 101, (i.1 * 101 + j.1 + 1) ^ 3 := by
    simp [h1]
    <;> try rfl
  rw [eq1]
  -- Lean can compute this arithmetic to verify divisibility.
  native_decide