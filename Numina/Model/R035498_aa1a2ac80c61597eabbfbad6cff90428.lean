import Mathlib

theorem algebra_124849 {p q r s : ℝ} (P : ℝ → ℝ)
    (hP : P = fun x => x^4 + p * x^3 + q * x^2 + r * x + s) :
    (∀ y : ℝ, ∃ A B C D : ℝ,
      A < B ∧ B < C ∧ C < D ∧
      P A = y ∧ P B = y ∧ P C = y ∧ P D = y ∧
      ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧
        (B - A) + (C - B) > z ∧ (C - B) + (D - C) > x ∧ (D - C) + (A - D) > y) ∨
    ¬∃ y : ℝ, ∃ A B C D : ℝ,
      A < B ∧ B < C ∧ C < D ∧
      P A = y ∧ P B = y ∧ P C = y ∧ P D = y ∧
      ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧
        (B - A) + (C - B) > z ∧ (C - B) + (D - C) > x ∧ (D - C) + (A - D) > y := by
  right
  intro h
  rcases h with ⟨y, A, B, C, D, h1, h2, h3, hP1, hP2, hP3, hP4, x, y1, z, hx, hy, hz, h4, h5, h6⟩
  have h7 : (D - C) + (A - D) = A - C := by
    linarith
  have h8 : A - C < 0 := by linarith
  linarith