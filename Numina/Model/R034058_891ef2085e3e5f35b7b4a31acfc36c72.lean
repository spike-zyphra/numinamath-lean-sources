import Mathlib

theorem algebra_20629 (total adults children : ℕ) (hpos : 0 < total ∧ 0 < adults ∧ 0 < children)
    (h1 : total = adults + children) (h2 : children = (adults / 4 : ℚ)) :
    children / total = (0.2 : ℚ) := by
  rcases hpos with ⟨htotal_pos, hadults_pos, hchildren_pos⟩
  have h3 : (adults : ℚ) = 4 * (children : ℚ) := by
    linarith
  have h4 : (total : ℚ) = (adults : ℚ) + (children : ℚ) := by
    exact_mod_cast h1
  have h5 : (total : ℚ) = 5 * (children : ℚ) := by
    rw [h4]
    rw [h3]
    linarith
  have h6 : (children : ℚ) / (total : ℚ) = (0.2 : ℚ) := by
    rw [h5]
    have h8 : (children : ℚ) ≠ 0 := by
      have h8 : (children : ℚ) > (0 : ℚ) := by
        exact_mod_cast show (children : ℕ) > (0 : ℕ) from hchildren_pos
      linarith
    field_simp at *
    <;> ring_nf <;> linarith
  exact_mod_cast h6