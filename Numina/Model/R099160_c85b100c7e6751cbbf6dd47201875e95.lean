import Mathlib

theorem number_theory_275835 (n : ℤ) (h : ¬ 3 ∣ n) : 3 ∣ n^2 - 1 := by
  have h1 : n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  rcases h1 with (h1 | h1)
  · -- Case where $n \equiv 1 \pmod{3}$:
    have h2 : n^2 % 3 = 1 := by
      have h1' : n % 3 = 1 := h1
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h1'] 
    omega 
  · -- Case where $n \equiv 2 \pmod{3}$:
    have h2 : n^2 % 3 = 1 := by
      have h1' : n % 3 = 2 := h1
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h1'] 
    omega