import Mathlib

def f (x y : ℝ) := x * y

theorem algebra_323671 {x : ℝ} (hx : f 2016 (f 6 x) = 100) :
    ∃ p q : ℕ, p > 0 ∧ q > 0 ∧ Nat.Coprime p q ∧ x = p / q := by 
  simp [f] at hx 
  have hx1 : x = 25 / 3024 := by 
    nlinarith 
    <;> norm_num at hx ⊢ 
  use 25, 3024 
  constructor 
  · norm_num 
  constructor 
  · norm_num 
  constructor 
  · norm_num 
  · rw [hx1] 
    all_goals norm_num