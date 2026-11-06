import Mathlib

theorem number_theory_239595 : IsGreatest { area | ∃ x y : ℕ, x.Prime ∧ y.Prime ∧ 2 * (x + y) = 40 ∧ area = x * y } 91:= by 
  constructor 
  · -- Show $91$ is obtained by $7$ and $13$.
    use 7, 13
    native_decide
  · -- Show 91 is the largest
    rintro area ⟨x, y, hx, hy, h1, h2⟩
    have h5 : x + y = 20 := by linarith
    have h6 : x ≤ 20 := by omega
    have h7 : y ≤ 20 := by omega
    interval_cases x <;> interval_cases y <;> norm_num at *
    <;> try { contradiction }
    <;> omega