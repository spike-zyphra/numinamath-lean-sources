import Mathlib

theorem algebra_327603 {a : ℝ} (A B : Set (ℝ × ℝ))
    (hA : A = {(x, y) | x + a^2 * y + 6 = 0})
    (hB : B = {(x, y) | (a - 2) * x + 3 * a * y + 2 * a = 0})
    (hAB : A ∩ B = ∅) :
    a = 0 ∨ a = -1 := by 
  by_contra h 
  push_neg at h 
  rcases h with ⟨ha1, ha2⟩ 
  have h3 : a + 1 ≠ 0 := by
    intro h
    apply ha2
    linarith
  have h4 : a ≠ 0 := ha1 
  have h5 : a * (a + 1) ≠ 0 := by
    apply mul_ne_zero 
    exact h4
    intro h6
    apply ha2
    linarith
  have h6 : ∃ p : ℝ × ℝ, p ∈ A ∩ B := by 
    use (-2 * (a + 3) / (a + 1), -4 / (a * (a + 1)))
    constructor 
    · -- Show the point is in A
      rw [hA]
      field_simp [(show a ≠ 0 by exact ha1), (show a + 1 ≠ 0 by intro h' ; apply ha2 ; linarith)]
      <;> ring_nf <;> field_simp [(show a ≠ 0 by exact ha1), (show a + 1 ≠ 0 by intro h' ; apply ha2; linarith)]
    · -- Show the point is in B
      rw [hB]
      field_simp [(show a ≠ 0 by exact ha1), (show a + 1 ≠ 0 by intro h' ; apply ha2; linarith)]
      <;> ring_nf <;> field_simp [(show a ≠ 0 by exact ha1), (show a + 1 ≠ 0 by intro h' ; apply ha2; linarith)]
  obtain ⟨p, hp⟩ := h6 
  have h3 : p ∈ A ∩ B := hp 
  rw [hAB] at h3 
  simp at h3