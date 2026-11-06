import Mathlib

theorem algebra_307085 : ¬∃ n : ℤ, (n^2 - n + 4) % 9 = 0 := by 
  intro h
  rcases h with ⟨n, hn⟩ 
  have h1 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by
    omega 
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> ( 
    simp [pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h1] at hn 
    all_goals omega
  )