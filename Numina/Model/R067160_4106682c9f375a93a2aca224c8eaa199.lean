import Mathlib

theorem algebra_80481 {w l x : ℕ} (hw : w > 0) (hl : l > 0)
    (h : (w + 1) * (l - 1) = w * l + x) :
    IsLeast {x | 0 < x ∧ ∃ w l : ℕ, w > 0 ∧ l > 0 ∧ (w + 1) * (l - 1) = w * l + x} 1 := by
  constructor
  · -- Show that 1 is indeed in the set
    constructor
    · norm_num
    · use 1, 3
      all_goals norm_num
  · -- Show that 1 is indeed the smallest
    rintro y ⟨hy, ⟨w', l', hw', hl', h_eq⟩⟩
    have h1 : y > 0 := hy
    omega