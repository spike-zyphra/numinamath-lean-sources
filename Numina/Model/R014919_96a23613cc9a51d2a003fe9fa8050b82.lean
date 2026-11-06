import Mathlib

theorem algebra_187566 {p : Polynomial ℤ} (h : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ p.eval x = 1 ∧ p.eval y = 1 ∧ p.eval z = 1) :
    ¬∃ r : ℤ, p.eval r = 0 := by
  rcases h with ⟨x, y, z, hxy, hyz, hzx, hp1, hp2, hp3⟩
  push_neg
  intro r hr
  have h1 : (r - x) ∣ (p.eval r - p.eval x) := by
    apply p.sub_dvd_eval_sub
  rw [show p.eval r = 0 by linarith [hr], hp1] at h1
  have h11 : (r - x) ∣ (-1 : ℤ) := by
    simpa using h1
  have h2 : (r - y) ∣ (p.eval r - p.eval y) := by
    apply p.sub_dvd_eval_sub
  rw [show p.eval r = 0 by linarith [hr], hp2] at h2
  have h22 : (r - y) ∣ (-1 : ℤ) := by
    simpa using h2
  have h3 : (r - z) ∣ (p.eval r - p.eval z) := by
    apply p.sub_dvd_eval_sub
  rw [show p.eval r = 0 by linarith [hr], hp3] at h3
  have h33 : (r - z) ∣ (-1 : ℤ) := by
    simpa using h3
  have h4 : (r - x) = 1 ∨ (r - x) = -1 := by
    have h41 : (r - x) ∣ 1 := by 
      exact Int.dvd_neg.mp h11
    have h42 : (r - x) = 1 ∨ (r - x) = -1 := by 
      have h43 : (r - x) ≤ 1 := by 
        apply Int.le_of_dvd (by norm_num) h41
      have h44 : (r - x) ≥ -1 := by 
        have h45 : -(r - x) ∣ 1 := by 
          exact Int.neg_dvd.2 h41
        have h46 : -(r - x) ≤ 1 := by 
          apply Int.le_of_dvd (by norm_num) h45
        omega
      interval_cases h : (r - x) <;> tauto
    exact h42
  have h5 : (r - y) = 1 ∨ (r - y) = -1 := by
    have h51 : (r - y) ∣ 1 := by 
      exact Int.dvd_neg.mp h22
    have h52 : (r - y) = 1 ∨ (r - y) = -1 := by 
      have h53 : (r - y) ≤ 1 := by 
        apply Int.le_of_dvd (by norm_num) h51
      have h54 : (r - y) ≥ -1 := by 
        have h55 : -(r - y) ∣ 1 := by 
          exact Int.neg_dvd.2 h51
        have h56 : -(r - y) ≤ 1 := by 
          apply Int.le_of_dvd (by norm_num) h55
        omega
      interval_cases h : (r - y) <;> tauto
    exact h52
  have h6 : (r - z) = 1 ∨ (r - z) = -1 := by
    have h61 : (r - z) ∣ 1 := by 
      exact Int.dvd_neg.mp h33
    have h62 : (r - z) = 1 ∨ (r - z) = -1 := by 
      have h63 : (r - z) ≤ 1 := by 
        apply Int.le_of_dvd (by norm_num) h61
      have h64 : (r - z) ≥ -1 := by 
        have h65 : -(r - z) ∣ 1 := by 
          exact Int.neg_dvd.2 h61
        have h66 : -(r - z) ≤ 1 := by 
          apply Int.le_of_dvd (by norm_num) h65
        omega
      interval_cases h : (r - z) <;> tauto
    exact h62
  omega