import Mathlib

theorem number_theory_7336 (x : ZMod 29) : x^2 = 22 ↔ x = 14 ∨ x = -14 := by
  constructor
  · -- Forward direction: if $x^2 \equiv 22 \pmod{29}$, then $x = \pm 14$.
    intro h
    have h1 : x^2 = 22 := h
    have h2 : x = 14 ∨ x = -14 := by 
      have h3 : x ^ 2 = 22 := h1
      have h4 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 ∨ x = 10 ∨ x = 11 ∨ x = 12 ∨ x = 13 ∨ x = 14 ∨ x = 15 ∨ x = 16 ∨ x = 17 ∨ x = 18 ∨ x = 19 ∨ x = 20 ∨ x = 21 ∨ x = 22 ∨ x = 23 ∨ x = 24 ∨ x = 25 ∨ x = 26 ∨ x = 27 ∨ x = 28 := by 
        fin_cases x <;> simp
      rcases h4 with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num at h3 ⊢
      <;> tauto
    tauto
  · -- Backward direction: If $x = \pm 14$, then $x^2 \equiv 22 \pmod{29}$.
    rintro (h | h)
    · -- Case $x = 14$.
      rw [h]
      native_decide
    · -- Case $x = -14$.
      rw [h]
      native_decide