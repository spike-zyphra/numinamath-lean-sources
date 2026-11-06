import Mathlib

/-
For the real number $a$ satisfying $0 \leq a \leq 4$, find the range of $x$ for which $x^2 + ax > 4x + a - 3$ always holds.
-/
theorem algebra_9463 :
    ∀ x, (∀ a : ℝ, 0 ≤ a ∧ a ≤ 4 → ( x ^ 2 + a * x > 4 * x + a - 3)) ↔ x > 3 ∨ x < -1 := by

  intro x

  -- auxiliary lemma
  have l_1 (x l r : ℝ) :
      0 < (x - l) * (x - r) ↔ (l < x ∧ r < x ∨ x < l ∧ x < r) := by
    constructor
    . intro h
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      . left; constructor <;> linarith
      . right; constructor <;> linarith
    . intro h
      apply mul_pos_iff.mpr
      simp_all

  -- Let $y = x^2 + ax - (4x + a - 3) = x^2 + ax - 4x - (a - 3)$
  let y (a : ℝ) := x ^ 2 + a * x - (4 * x + a - 3)

  -- $y = (x - 1) * (x - (3 - a))$
  have hy : ∀ a, y a = (x - 1) * (x - (3 - a)) := by intro; ring


  constructor

  . intro h

    have h0 := h 0
    have h1 := h 4
    apply not_or_of_imp at h1
    simp at h0 h1

    have h_ypos0 : 0 < y 0 := by dsimp [y]; linarith
    have h_ypos1 : 0 < y 4 := by dsimp [y]; linarith
    rw [hy] at h_ypos0 h_ypos1


    -- Therefore, the solutions are $x > 1$ and $x > 3 - a$ (1), or $x < 1$ and $x < 3 - a$ (2)
    rcases (l_1 x 1 (3 - 0)).mp h_ypos0
    -- In (1), it requires $x$ to be greater than the larger number between 1 and $3 - a$, and the maximum value of $3 - a$ is 3, hence $x > 3$;
    . left
      linarith
    -- In (2), it requires $x$ to be less than the smaller number between 1 and $3 - a$, and the minimum value of $3 - a$ is $-1$, hence $x < -1$;
    . right
      rcases (l_1 x 1 (3 - 4)).mp h_ypos1
      <;> linarith

  -- verify that $x > 3 ∨ x < -1$ satisfies the restriction
  . intro hx
    intro a ⟨ha1, ha2⟩
    apply lt_add_neg_iff_lt.mp
    specialize hy a
    dsimp [y] at hy
    rw [sub_eq_add_neg] at hy
    rw [hy]
    apply (l_1 x _ _).mpr
    rcases hx with hx | hx
    . left
      constructor
      <;> linarith
    . right
      constructor
      <;> linarith

