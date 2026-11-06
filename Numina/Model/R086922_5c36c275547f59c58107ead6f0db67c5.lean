import Mathlib

theorem algebra_239338 {g b : ℕ} (hg : g * 200 + b * 300 = 1700) (hb : b + g > 0)
    (hodd : Odd (b + g)) : g = 4 ∧ b = 3 := by 
  have h1 : g * 200 + b * 300 = 1700 := hg 
  have h2 : g ≤ 8 := by 
    omega
  have h3 : b ≤ 5 := by 
    omega
  have h4 : (b + g) % 2 = 1 := by
    rcases hodd with ⟨k, hk⟩
    omega
  interval_cases g <;> interval_cases b
  <;> norm_num at h1 h4 <;> tauto