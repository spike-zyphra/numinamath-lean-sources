import Mathlib

theorem number_theory_77628 :
    ¬∃ x y : ℤ, 0 < x ∧ 0 < y ∧ ∃ m n : ℕ,
      m^2 = x^2 + y + 2 ∧ n^2 = y^2 + 4 * x := by 
  rintro ⟨x, y, hx, hy, ⟨m, n, hm, hn⟩⟩
  have h1 : (m : ℤ) ^ 2 = x^2 + y + 2 := by
    exact_mod_cast hm
  have h2 : (n : ℤ) ^ 2 = y^2 + 4 * x := by
    exact_mod_cast hn
  have h3 : (m : ℤ) > x := by
    nlinarith
  have h4 : (n : ℤ) > y := by
    nlinarith
  have h5 : (n : ℤ) < y + 2 := by
    nlinarith [sq_nonneg (y - (n : ℤ) : ℤ), sq_pos_of_pos hx, sq_pos_of_pos hy]
  have h6 : (n : ℤ) = y + 1 := by
    have h7 : (n : ℤ) > y := by linarith
    have h8 : (n : ℤ) ≤ y + 1 := by
      nlinarith
    omega
  rw [h6] at h2
  have h8 : 2 * y + 1 = 4 * x := by 
    nlinarith
  omega