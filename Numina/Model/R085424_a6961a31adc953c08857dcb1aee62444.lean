import Mathlib

theorem algebra_196823 {P : ℤ} (hP : 5 < P ∧ P < 20) (hroots : ∃ x y : ℤ, x^2 - 2*(2*P-3)*x + 4*P^2 - 14*P + 8 = 0 ∧ y^2 - 2*(2*P-3)*y + 4*P^2 - 14*P + 8 = 0) :
    P = 12 := by
  have h1 : 5 < P := hP.1
  have h2 : P < 20 := hP.2
  rcases hroots with ⟨x, y, hx, hy⟩
  have h3 : P > 5 := by linarith
  have h4 : P < 20 := by linarith
  have h5 : P = 6 ∨ P = 7 ∨ P = 8 ∨ P = 9 ∨ P = 10 ∨ P = 11 ∨ P = 12 ∨ P = 13 ∨ P = 14 ∨ P = 15 ∨ P = 16 ∨ P = 17 ∨ P = 18 ∨ P = 19 := by omega
  rcases h5 with (r | r | r | r | r | r | r | r | r | r | r | r | r | r) <;> ( 
    rw [r] at hx hy 
    <;> ( 
      norm_num at hx hy 
      <;> ( 
        have h6 : x ≤ 45 := by nlinarith
        have h7 : x ≥ -30 := by nlinarith
        interval_cases x <;> omega
      )
    )
  )