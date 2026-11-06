import Mathlib

theorem algebra_20692 {P : ℝ → ℝ} (a b c d :ℝ) (hP : ∃ a b c d, P = fun x => a*x^3 + b*x^2 + c*x + d)
    (hP0 : P 0 = -3) (hP1 : P 1 = 4) (hP2 : ∃ e f, ∀ x : ℝ, P x = (e * x + f) * (x ^ 2 + x + 1) + 2 * x - 1) (hP3 : ∀ x : ℝ, P x = (a * x + b) * (x ^ 2 + x + 1) + c * x + d) : a = 3 ∧ b = -2 := by
  have eq1 := hP3 0 
  simp at eq1 
  have eq2 := hP3 1
  simp at eq2 
  rcases hP2 with ⟨e, f, hP2⟩
  have eq3 := hP2 0
  simp at eq3 
  have eq4 := hP2 1 
  simp at eq4 
  have eq5 := hP2 2 
  ring_nf at eq5 
  have eq6 := hP2 (-1) 
  ring_nf at eq6 
  have eq7 := hP3 2 
  ring_nf at eq7 
  have eq8 := hP3 (-1) 
  ring_nf at eq8 
  rcases hP with ⟨a', b', c', d', hP'⟩ 
  have eq11 : P 0 = a' * 0 ^ 3 + b' * 0 ^ 2 + c' * 0 + d' := by 
    simp [hP']
  have eq12 : P 1 = a' * 1 ^ 3 + b' * 1 ^ 2 + c' * 1 + d' := by 
    simp [hP']
  have eq13 : P 2 = a' * 2 ^ 3 + b' * 2 ^ 2 + c' * 2 + d' := by 
    simp [hP']
  have eq14 : P (-1) = a' * (-1) ^ 3 + b' * (-1) ^ 2 + c' * (-1) + d' := by 
    simp [hP']
  constructor 
  · -- Prove $a = 3$
    ring_nf at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq11 eq12 eq13 eq14 
    nlinarith
  · -- Prove $b = -2$
    ring_nf at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq11 eq12 eq13 eq14 
    nlinarith