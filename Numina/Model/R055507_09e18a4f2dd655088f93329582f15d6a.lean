import Mathlib

theorem algebra_10479 {Z W lambda : ℂ} (hl : lambda ≠ 1) :
    (Z = (lambda * W) / (1 - Complex.abs lambda ^ 2)) ↔
    (Z = (lambda * W) / (1 - Complex.abs lambda ^ 2) ∧
     Complex.abs (Z - (lambda * W) / (1 - Complex.abs lambda ^ 2)) = 0) := by
  constructor
  · -- Forward: If $P$ then $P ∧ Q$
    intro h
    constructor
    · -- Proof of $P$
      exact h
    · -- Now need to prove $Complex.abs (Z - (lambda * W) / (1 - Complex.abs lambda ^ 2)) = 0$
      have h1 : Z - (lambda * W) / (1 - Complex.abs lambda ^ 2) = 0 := by
        rw [h]
        ring_nf
        <;> norm_num [Complex.ext_iff]
      rw [h1]
      simp
  · -- Backward: If $P ∧ Q$ then $P$
    rintro ⟨h, _⟩
    exact h