import Mathlib

theorem number_theory_282727 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 = z^2) :
    (3 ∣ x ∨ 3 ∣ y ∨ 3 ∣ z) ∧ (4 ∣ x ∨ 4 ∣ y ∨ 4 ∣ z) ∧
    (5 ∣ x ∨ 5 ∣ y ∨ 5 ∣ z) := by
  have h1 : 3 ∣ x ∨ 3 ∣ y ∨ 3 ∣ z := by
    by_contra h1
    push_neg at h1
    have h2 : x % 3 = 1 ∨ x % 3 = 2 := by
      omega
    have h3 : y % 3 = 1 ∨ y % 3 = 2 := by
      omega
    have h4 : z % 3 = 1 ∨ z % 3 = 2 := by
      omega
    have hx2 : x ^ 2 % 3 = 1 := by
      rcases h2 with (h2 | h2)
      · -- x % 3 = 1, then x^2 % 3 = 1^2 % 3 = 1
        simp [Nat.pow_mod, h2, Nat.mul_mod, Nat.add_mod]
      · -- x % 3 = 2, then x^2 % 3 = 4 % 3 = 1
        simp [Nat.pow_mod, h2, Nat.mul_mod, Nat.add_mod]
    have hy2 : y ^ 2 % 3 = 1 := by
      rcases h3 with (h3 | h3)
      · -- y % 3 = 1, then y^2 % 3 = 1^2 % 3 = 1
        simp [Nat.pow_mod, h3, Nat.mul_mod, Nat.add_mod]
      · -- y % 3 = 2, then y^2 % 3 = 4 % 3 = 1
        simp [Nat.pow_mod, h3, Nat.mul_mod, Nat.add_mod]
    have hz2 : z ^ 2 % 3 = 1 := by
      rcases h4 with (h4 | h4)
      · -- z % 3 = 1, then z^2 % 3 = 1^2 % 3 = 1
        simp [Nat.pow_mod, h4, Nat.mul_mod, Nat.add_mod]
      · -- z % 3 = 2, then z^2 % 3 = 4 % 3 = 1
        simp [Nat.pow_mod, h4, Nat.mul_mod, Nat.add_mod]
    have h2 : (x ^ 2 + y ^ 2) % 3 = z ^ 2 % 3 := by
      omega
    omega
  have h2 : 4 ∣ x ∨ 4 ∣ y ∨ 4 ∣ z := by
    by_contra h2
    push_neg at h2
    have h3 : x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
      omega
    have h4 : y % 8 = 1 ∨ y % 8 = 2 ∨ y % 8 = 3 ∨ y % 8 = 5 ∨ y % 8 = 6 ∨ y % 8 = 7 := by
      omega
    have h5 : z % 8 = 1 ∨ z % 8 = 2 ∨ z % 8 = 3 ∨ z % 8 = 5 ∨ z % 8 = 6 ∨ z % 8 = 7 := by
      omega
    have hx2 : x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3) <;> norm_num [h3, Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at *
    have hy2 : y ^ 2 % 8 = 1 ∨ y ^ 2 % 8 = 4 := by
      rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4) <;> norm_num [h4, Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at *
    have hz2 : z ^ 2 % 8 = 1 ∨ z ^ 2 % 8 = 4 := by
      rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5) <;> norm_num [h5, Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at *
    have h6 : (x ^ 2 + y ^ 2) % 8 = z ^ 2 % 8 := by
      omega
    omega
  have h3 : 5 ∣ x ∨ 5 ∣ y ∨ 5 ∣ z := by
    by_contra h3
    push_neg at h3
    have h4 : x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
      omega
    have h5 : y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by
      omega
    have h6 : z % 5 = 1 ∨ z % 5 = 2 ∨ z % 5 = 3 ∨ z % 5 = 4 := by
      omega
    have hx2 : x ^ 2 % 5 = 1 ∨ x ^ 2 % 5 = 4 := by
      rcases h4 with (h4 | h4 | h4 | h4) <;> norm_num [h4, Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at *
    have hy2 : y ^ 2 % 5 = 1 ∨ y ^ 2 % 5 = 4 := by
      rcases h5 with (h5 | h5 | h5 | h5) <;> norm_num [h5, Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at *
    have hz2 : z ^ 2 % 5 = 1 ∨ z ^ 2 % 5 = 4 := by
      rcases h6 with (h6 | h6 | h6 | h6) <;> norm_num [h6, Nat.pow_mod, Nat.mul_mod, Nat.add_mod] at *
    have h7 : (x ^ 2 + y ^ 2) % 5 = z ^ 2 % 5 := by
      omega
    omega
  constructor
  · -- First part of the conjunction
    tauto
  constructor
  · -- Second part of the conjunction
    tauto
  · -- Third part of the conjunction
    tauto