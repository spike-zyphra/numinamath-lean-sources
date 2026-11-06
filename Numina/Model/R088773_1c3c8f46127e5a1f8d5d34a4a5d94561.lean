import Mathlib

theorem algebra_255645 (a b c : ℝ) (A B C : ℝ → ℝ → ℝ)
    (hA : A = fun x y => 10 * x ^ 2 - 6 * x * y + 3 * y ^ 2)
    (hB : B = fun x y => a * x ^ 2 + b * x * y + c * y ^ 2)
    (hC : C = fun x y => 15 * y ^ 4 - 36 * x * y ^ 3 + 62 * x ^ 2 * y ^ 2 - 20 * x ^ 3 * y)
    (hAB : ∀ x y, A x y * B x y = C x y) :
    a = 0 ∧ b = -2 ∧ c = 5 := by

  have eq1 := hAB 0 1
  simp [hA, hB, hC] at eq1
  have eq2 := hAB 1 0
  simp [hA, hB, hC] at eq2
  have eq3 := hAB 1 1
  simp [hA, hB, hC] at eq3
  have eq4 : c = 5 := by
    nlinarith
  have ha : a = 0 := by 
    linarith
  have hb : b = -2 := by
    rw [ha, eq4] at eq3
    linarith
  exact ⟨ha, hb, eq4⟩