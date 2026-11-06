import Mathlib

theorem algebra_586 {n b : ℕ} (hb : 0 < b) (h1 : (b + 1) ∣ n ∧ n / (b + 1) = 6) (h2 : (b - 1) ∣ n ∧ n / (b - 1) = 9) : n = 36 := by 
  rcases h1 with ⟨h11, h12⟩
  rcases h2 with ⟨h21, h22⟩
  have hc1 : n = 6 * (b + 1) := by 
    have h : n = 6 * (b + 1) := by
      rw [←h12]
      field_simp [Nat.div_mul_cancel h11]
    exact h
  have hc2 : n = 9 * (b - 1) := by 
    have h : n = 9 * (b - 1) := by 
      rw [←h22]
      field_simp [Nat.div_mul_cancel h21]
    exact h 
  have hb1 : b = 5 := by 
    omega
  rw [hb1] at hc1
  norm_num at hc1
  exact hc1