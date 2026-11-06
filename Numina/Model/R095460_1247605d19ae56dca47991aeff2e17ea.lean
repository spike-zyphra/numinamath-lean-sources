import Mathlib

theorem algebra_21209 (x : ℝ) (hx : x ≠ -2 ∧ x ≠ -9 ∧ x ≠ -3 ∧ x ≠ -8) :
    (x + 1) / (x + 2) + (x + 8) / (x + 9) = (x + 2) / (x + 3) + (x + 7) / (x + 8) ↔
    x = -11 / 2 := by
  constructor
  · -- Proof of forward direction: equation implies x = -11/2
    intro heq
    rcases hx with ⟨h₁, h₂, h₃, h₄⟩
    field_simp [(show x + 2 ≠ 0 by intro h; apply h₁; linarith),
        (show x + 9 ≠ 0 by intro h; apply h₂; linarith),
        (show x + 3 ≠ 0 by intro h; apply h₃; linarith),
        (show x + 8 ≠ 0 by intro h; apply h₄; linarith)] at heq
    ring_nf at heq
    linarith
  · -- Proof of reverse direction: x = -11/2 implies equation
    intro he
    rcases hx with ⟨h₁, h₂, h₃, h₄⟩
    rw [he]
    norm_num