import Mathlib

theorem algebra_169446 (x y : ℕ) : 2 * x + 3 * y = 27 ↔
    (x, y) = (0, 9) ∨ (x, y) = (3, 7) ∨ (x, y) = (6, 5) ∨ (x, y) = (9, 3) ∨ (x, y) = (12, 1) := by
  constructor
  · -- Forward: if the equation holds, then (x,y) is one of the given pairs
    intro h
    have h1 : y ≤ 9 := by
      omega
    have h2 : x ≤ 13 := by
      omega
    have : (x, y) = (0, 9) ∨ (x, y) = (3, 7) ∨ (x, y) = (6, 5) ∨ (x, y) = (9, 3) ∨ (x, y) = (12, 1) := by
      simp [Prod.ext_iff]
      omega
    exact this
  · -- Backward: if (x,y) is one of the given pairs, then the equation holds
    rintro (h | h | h | h | h)
    · -- Case (0, 9)
      simp [Prod.mk.injEq] at h ⊢
      all_goals omega
    · -- Case (3, 7)
      simp [Prod.mk.injEq] at h ⊢
      all_goals omega
    · -- Case (6, 5)
      simp [Prod.mk.injEq] at h ⊢
      all_goals omega
    · -- Case (9, 3)
      simp [Prod.mk.injEq] at h ⊢
      all_goals omega
    · -- Case (12, 1)
      simp [Prod.mk.injEq] at h ⊢
      all_goals omega