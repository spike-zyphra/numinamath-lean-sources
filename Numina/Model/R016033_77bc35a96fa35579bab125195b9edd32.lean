import Mathlib

theorem number_theory_295757 {x y z : ℤ} (h : x^2 + y^2 = z^2) : 2 ∣ x ∨ 2 ∣ y := by 
  by_contra h1
  push_neg at h1
  have hx1 : x % 2 = 1 := by 
    by_contra h2
    push_neg at h2
    have h3 : 2 ∣ x := by
      omega
    tauto
  have hy1 : y % 2 = 1 := by 
    by_contra h2
    push_neg at h2
    have h3 : 2 ∣ y := by
      omega
    tauto
  have h4 : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by
    omega
  have h5 : y % 8 = 1 ∨ y % 8 = 3 ∨ y % 8 = 5 ∨ y % 8 = 7 := by
    omega
  -- Let's then compute their squares modulo 8.
  have h6 : x^2 % 8 = 1 := by
    rcases h4 with (h4 | h4 | h4 | h4) <;> 
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h4]
    all_goals omega
  have h7 : y^2 % 8 = 1 := by
    rcases h5 with (h5 | h5 | h5 | h5) <;> 
      norm_num [pow_two, Int.add_emod, Int.mul_emod, h5]
    all_goals omega
  have h8 : (x ^ 2 + y ^ 2) % 8 = 2 := by 
    omega
  -- Now let's look at z.
  have h9 : z^2 % 8 = 0 ∨ z^2 % 8 = 1 ∨ z^2 % 8 = 4 := by
    have h10 : z % 8 = 0 ∨ z % 8 = 1 ∨ z % 8 = 2 ∨ z % 8 = 3 ∨ z % 8 = 4 ∨ z % 8 = 5 ∨ z % 8 = 6 ∨ z % 8 = 7 := by
      omega
    rcases h10 with (h10 | h10 | h10 | h10 | h10 | h10 | h10 | h10) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h10] at *
    all_goals omega
  -- Contradicts with (x^2 + y^2) % 8 = 2
  have h10 : (x ^ 2 + y ^ 2) % 8 = z^2 % 8 := by
    omega
  omega