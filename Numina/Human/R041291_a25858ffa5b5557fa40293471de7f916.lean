import Mathlib
/-if the fraction an+b/cn+d may be simplified using 2(as a commom divisor), show that the number ad-bc is even (a b c d are natural numbers and the cn+d different from zero)-/
theorem algebra_38102 {a b c d n : ℕ} 
    (h'' : 2 ∣ (a * n + b)) (h''' : 2 ∣ (c * n + d)) :
    Even (a * d - b * c) := by
  have h1 : (a * n + b) % 2 = 0 := by 
    omega
  have h2 : (c * n + d) % 2 = 0 := by 
    omega
  have h3 : (a * n) % 2 = (b % 2) := by 
    omega
  have h4 : (c * n) % 2 = (d % 2) := by 
    omega
  have h5 : (a * d) % 2 = (b * c) % 2 := by 
    have h5 : n % 2 = 0 ∨ n % 2 = 1 := by 
      omega
    cases h5 with
    | inl hn0 =>
      have hbn : b % 2 = 0 := by 
        have : (a * n) % 2 = 0 := by 
          simp [hn0, Nat.mul_mod, Nat.add_mod] at h3
          omega
        omega
      have hdn : d % 2 = 0 := by 
        have : (c * n) % 2 = 0 := by 
          simp [hn0, Nat.mul_mod, Nat.add_mod] at h4
          omega
        omega
      have h6 : (a * d) % 2 = 0 := by 
        simp [Nat.mul_mod, hdn]
      have h7 : (b * c) % 2 = 0 := by 
        simp [Nat.mul_mod, hbn]
      omega
    | inr hn1 =>
      have hbn : b % 2 = a % 2 := by 
        simp [hn1, Nat.mul_mod, Nat.add_mod] at h3
        omega
      have hdn : d % 2 = c % 2 := by 
        simp [hn1, Nat.mul_mod, Nat.add_mod] at h4
        omega
      have h6 : (a * d) % 2 = (b * c) % 2 := by 
        simp [Nat.mul_mod, hbn, hdn]
      exact h6
  exact ⟨(a * d - b * c) / 2, by omega⟩