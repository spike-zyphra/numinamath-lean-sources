import Mathlib

theorem algebra_279468 {k : ℝ} (h : ∃ x y, x ≠ y ∧ x^2 - 402 * x + k = 0 ∧ y^2 - 402 * y + k = 0 ∧ x + 3 = 80 * y) :
    k = 1985 := by
  rcases h with ⟨x, y, hxy, hx, hy, hx3⟩
  have h1 : x^2 - y^2 - 402 * (x - y) = 0 := by
    nlinarith
  have h2 : (x - y) * (x + y - 402) = 0 := by
    ring_nf at h1 ⊢
    linarith
  cases' (mul_eq_zero.1 h2) with h3 h4
  · -- contradiction, since x ≠ y
    exfalso
    apply hxy
    linarith
  · -- we have $x + y = 402$
    have hxy2 : x + y = 402 := by linarith
    have hx2 : x = 80 * y - 3 := by linarith
    -- substitute $x = 80 \cdot y - 3$ into $x + y = 402$, to get $81 \cdot y = 405$, so $y = 5$
    -- and then $x = 397$.
    have hy2 : y = 5 := by
      rw [hx2] at hxy2
      linarith
    have hx3' : x = 397 := by
      rw [hy2] at hx2
      linarith
    rw [hx3'] at hx
    nlinarith