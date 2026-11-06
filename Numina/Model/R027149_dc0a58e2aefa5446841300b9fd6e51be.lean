import Mathlib

theorem number_theory_111674 {a b d x y : ℕ} (h₀ : d = Nat.gcd a b) (h₁ : a = d * x) (h₂ : b = d * y)
    (h₃ : x.gcd y = 1) (h₄ : 5 * d * x + 3 * d * y = 150) (h₅ : d * x * y = 15 * d) :
    (a = 3 ∧ b = 45) ∨ (a = 15 ∧ b = 25) := by
  have h6 : x * y = 15 := by
    have h7 : d ≠ 0 := by
      by_contra h
      rw [h] at h₄ h₅
      nlinarith
    have h8 : x * y = 15 := by
      have h9 : d ≠ 0 := h7
      have h10 : d * (x * y) = 15 * d := by
        linarith [h₅]
      have h11 : x * y = 15 := by
        apply (mul_left_inj' h9).mp
        linarith
      linarith
    linarith
  have h7 : x ≤ 15 := by
    have h7' : x ∣ 15 := by
      use y
      linarith [h6]
    exact Nat.le_of_dvd (by norm_num) h7'
  have h8 : y ≤ 15 := by
    have h8' : y ∣ 15 := by
      use x
      linarith [h6]
    exact Nat.le_of_dvd (by norm_num) h8'
  interval_cases x <;> interval_cases y
  <;> norm_num [Nat.mul_comm] at h₃ h₄ h6 ⊢
  <;> omega