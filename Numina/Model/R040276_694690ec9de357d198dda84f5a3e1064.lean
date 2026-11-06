import Mathlib

theorem number_theory_7919
    (x y z : ℤ)
    (h : (x - y) * (y - z) * (z - x) = x + y + z) :
    27 ∣ x + y + z := by
  have h1 : (x - y) * (y - z) * (z - x) = x + y + z := h

  have h2 : x % 3 = y % 3 := by
    have h1' : (x - y) * (y - z) * (z - x) % 3 = (x + y + z) % 3 := by
      omega
    have h21 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by 
      omega
    have h22 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by
      omega
    have h23 : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by
      omega
    rcases h21 with (h21 | h21 | h21) <;> rcases h22 with (h22 | h22 | h22) <;> rcases h23 with (h23 | h23 | h23) <;> 
      norm_num [Int.add_emod, Int.mul_emod, Int.sub_emod, h21, h22, h23] at h1' <;> 
      omega
    all_goals omega
  -- Similarly for y and z
  have h2' : y % 3 = z % 3 := by
    have h1' : (x - y) * (y - z) * (z - x) % 3 = (x + y + z) % 3 := by
      omega
    have h21 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by 
      omega
    have h22 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by
      omega
    have h23 : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by
      omega
    rcases h21 with (h21 | h21 | h21) <;> rcases h22 with (h22 | h22 | h22) <;> rcases h23 with (h23 | h23 | h23) <;> 
      norm_num [Int.add_emod, Int.mul_emod, Int.sub_emod, h21, h22, h23] at h1' <;> 
      omega
    all_goals omega
  -- From these, we can show 3 divides the differences
  have h3 : 3 ∣ x - y := by 
    omega
  have h3' : 3 ∣ y - z := by 
    omega
  -- Similarly for z - x
  have h3'' : 3 ∣ z - x := by 
    omega
  -- Therefore, 27 divides the product
  rcases h3 with ⟨k1, hk1⟩
  rcases h3' with ⟨k2, hk2⟩
  rcases h3'' with ⟨k3, hk3⟩
  have h4 : (x - y) * (y - z) * (z - x) = 27 * (k1 * k2 * k3) := by 
    rw [show (x - y) = 3 * k1 by linarith, show (y - z) = 3 * k2 by linarith, show (z - x) = 3 * k3 by linarith]
    ring_nf
    <;> nlinarith
  -- Therefore, 27 divides the sum
  rw [h4] at h
  use k1 * k2 * k3
  linarith