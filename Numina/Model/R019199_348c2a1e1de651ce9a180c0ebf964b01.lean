import Mathlib

theorem algebra_312314 {x y : ℝ} (h1 : abs x + y = 12) (h2 : x + abs y = 6) :
    (x, y) = (6 - abs y, abs y) := by
  have h3 : x = 6 - abs y := by linarith
  simp [Prod.ext_iff, h3]
  <;> try { 
    cases' abs_cases y with hy hy
    <;> try cases' abs_cases x with hx hx
    <;> try { 
      linarith 
    }
  }
  <;> try { linarith }