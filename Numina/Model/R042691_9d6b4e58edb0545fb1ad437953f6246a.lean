import Mathlib

theorem number_theory_129486 (n : ℕ) :
    Nat.Coprime (21*n + 4) (14*n + 3) := by 
  show Nat.Coprime (21 * n + 4) (14 * n + 3)
  have h1 : Nat.Coprime (21 * n + 4) (14 * n + 3) := by 
    have h2 : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
      have eq1 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (21 * n + 4) := by 
        exact Nat.gcd_dvd_left (21 * n + 4) (14 * n + 3)
      have eq2 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (14 * n + 3) := by 
        exact Nat.gcd_dvd_right (21 * n + 4) (14 * n + 3)
      have h3 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 1 := by
        have h3 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (3 * (14 * n + 3)) := by
          apply Nat.dvd_trans eq2 
          simp 
        have h4 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (2 * (21 * n + 4)) := by 
          apply Nat.dvd_trans eq1 
          simp 
        have eq5 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (3 * (14 * n + 3) - (2 * (21 * n + 4))) := by 
          apply Nat.dvd_sub' 
          exact h3 
          exact h4 
        have eq8 : 3 * (14 * n + 3) - (2 * (21 * n + 4)) = 1 := by 
          omega 
        rw [eq8] at eq5 
        exact eq5 
      have h5 : Nat.gcd (21 * n + 4) (14 * n + 3) ≤ 1 := by 
        exact Nat.le_of_dvd (by norm_num) h3 
      interval_cases (Nat.gcd (21 * n + 4) (14 * n + 3) ) <;> norm_num at * 
    rw [Nat.coprime_iff_gcd_eq_one] 
    exact h2 
  exact h1