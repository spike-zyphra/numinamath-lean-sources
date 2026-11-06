import Mathlib

/- Given that the roots of the equation ${{x}^{2}}-6x-4{{n}^{2}}-32n=0$ with respect to $x$ are integers, find the value of the integer $n$. -/
theorem  number_theory_626484 {n : ℤ}
  (hn : ∃ x y : ℤ, x ≠ y ∧ x^2 - 6*x - 4*n^2 - 32*n = 0
                         ∧ y^2 - 6*y - 4*n^2 - 32*n = 0)
  : n ∈ ({10, 0, -18, -8} : Set _):=
by
  rcases hn with ⟨x, y, hxy, hx, hy⟩
  -- x^2 - y^2 -6*(x - y) = 0
  have : (x - y) * (x + y - 6) = 0 := by
    nlinarith
  have : x + y - 6 = 0 := by
    apply_fun (λ z => z / (x - y)) at this
    field_simp [sub_ne_zero.mpr hxy] at this
    linarith
  have : y = 6 - x := by linarith
  rw [this] at hy
  -- (x - 3)^2 = 4n^2 + 32n + 9
  have : (x - 3)^2 = 4 * n^2 + 32 * n + 9 := by
    nlinarith [hx]
  have : (2 * n + 8)^2 - (x - 3)^2 = 55 := by
    nlinarith [this]
  -- solve Diophantine equation
  have : (2*n + 8 + x - 3) * (2* n + 8 - (x - 3)) = 55 := by
    ring_nf at this
    ring_nf
    linarith
  have H : (2 * n + 8 + x - 3) ∣ 55 := by
    use (2 * n + 8 - (x - 3))
    linarith
  -- Now we can show the upper bound
  have : (2 * n + 8 + x - 3) ≤ 55 := by
    apply Int.le_of_dvd (by norm_num) H
  -- And the lower bound
  have : (2 * n + 8 + x - 3) ≥ -55 := by
    have : -(2 * n + 8 + x - 3) ∣ 55 := by
      apply Int.neg_dvd.mpr
      assumption
    have : -(2 * n + 8 + x - 3) ≤ 55 := by
      apply Int.le_of_dvd (by norm_num) this
    linarith
  -- Here we have the range of (2 * n + 8 + x - 3)
  -- simply try each one
  simp
  interval_cases h : (2 * n + 8 + x - 3) <;> try omega
