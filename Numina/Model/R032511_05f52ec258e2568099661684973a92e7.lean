import Mathlib

theorem number_theory_45461 (x y z : ℤ) (h : x^3 + y^3 = z^3) :
    3 ∣ x ∨ 3 ∣ y ∨ 3 ∣ z := by
  by_contra h1
  push_neg at h1
  have h2 : ¬ (3 ∣ x) := by tauto
  have h3 : ¬ (3 ∣ y) := by tauto
  have h4 : ¬ (3 ∣ z) := by tauto
  have h5 : x % 3 = 1 ∨ x % 3 = 2 := by 
    omega
  have h6 : y % 3 = 1 ∨ y % 3 = 2 := by 
    omega
  have h7 : z  % 3 = 1 ∨ z  % 3 = 2 := by 
    omega
  have h8 : x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 7 ∨ x % 9 = 8 := by
    omega
  have h9 : y  % 9 = 1 ∨ y  % 9 = 2 ∨ y  % 9 = 4 ∨ y  % 9 = 5 ∨ y  % 9 = 7 ∨ y  % 9 = 8 := by 
    omega
  have h10 : z  % 9 = 1 ∨ z  % 9 = 2 ∨ z  % 9 = 4 ∨ z  % 9 = 5 ∨ z  % 9 = 7 ∨ z  % 9 = 8 := by 
    omega
  have h11 : x^3  % 9 = 1 ∨ x^3  % 9 = 8 := by 
    rcases h8 with (h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
  have h12 : y^3  % 9 = 1 ∨ y^3  % 9 = 8 := by 
    rcases h9 with (h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
  have h13 : z^3  % 9 = 1 ∨ z^3  % 9 = 8 := by 
    rcases h10 with (h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
  have h14 : (x^3 + y^3) % 9 = z^3  % 9 := by 
    omega
  omega