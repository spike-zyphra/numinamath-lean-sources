import Mathlib

open Polynomial

theorem number_theory_62496 {P : ℤ[X]} (hP : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ P.eval x = 0 ∧ P.eval y = 0 ∧ P.eval z = 0) :
    ∀ n, P.eval n ≠ 1 := by
  rcases hP with ⟨x, y, z, h1, h2, h3, hx, hy, hz⟩
  intro n 
  by_contra h
  have h4 : (n - x) ∣ (P.eval n - P.eval x) := by 
    apply Polynomial.sub_dvd_eval_sub n x P
  have h5 : (n - y) ∣ (P.eval n - P.eval y) := by 
    apply Polynomial.sub_dvd_eval_sub n y P
  have h6 : (n - z) ∣ (P.eval n - P.eval z) := by 
    apply Polynomial.sub_dvd_eval_sub n z P
  -- Now since we have $P(n) = 1$ and $P(x) = 0$
  have eq1 : P.eval n - P.eval x = 1 := by 
    rw [show P.eval x = 0 by simpa using hx, h]
    all_goals omega
  have eq2 : P.eval n - P.eval y = 1 := by 
    rw [show P.eval y = 0 by simpa using hy, h]
    all_goals omega
  have eq3 : P.eval n - P.eval z = 1 := by 
    rw [show P.eval z = 0 by simpa using hz, h]
    all_goals omega
  have h7 : (n - x) ∣ 1 := by
    rw [eq1] at h4
    exact h4
  have h8 : (n - y) ∣ 1 := by
    rw [eq2] at h5
    exact h5
  have h9 : (n - z) ∣ 1 := by
    rw [eq3] at h6
    exact h6
  have h10 : (n - x) = 1 ∨ (n - x) = -1 := by
    have : (n - x) ≤ 1 := by
      apply Int.le_of_dvd (by norm_num) h7
    have : (n - x) ≥ -1 := by
      have h8' : (- (n - x)) ∣ 1 := by 
        exact Int.neg_dvd.2 h7
      have h8'' : (- (n - x)) ≤ 1 := by
        apply Int.le_of_dvd (by norm_num) h8'
      omega
    interval_cases h : (n - x) <;> try { 
      tauto 
    } <;> try { 
      exfalso 
      <;> try { 
        tauto 
      } 
      <;> try { 
        omega 
      }
    }
  have h11 : (n - y) = 1 ∨ (n - y) = -1 := by
    have : (n - y) ≤ 1 := by
      apply Int.le_of_dvd (by norm_num) h8
    have : (n - y) ≥ -1 := by
      have h8' : (- (n - y)) ∣ 1 := by 
        exact Int.neg_dvd.2 h8
      have h8'' : (- (n - y)) ≤ 1 := by
        apply Int.le_of_dvd (by norm_num) h8'
      omega
    interval_cases h : (n - y) <;> try { 
      tauto 
    } <;> try { 
      exfalso 
      <;> try { 
        tauto 
      } 
      <;> try { 
        omega 
      }
    }
  have h12 : (n - z) = 1 ∨ (n - z) = -1 := by
    have : (n - z) ≤ 1 := by
      apply Int.le_of_dvd (by norm_num) h9
    have : (n - z) ≥ -1 := by
      have h8' : (- (n - z)) ∣ 1 := by 
        exact Int.neg_dvd.2 h9
      have h8'' : (- (n - z)) ≤ 1 := by
        apply Int.le_of_dvd (by norm_num) h8'
      omega
    interval_cases h : (n - z) <;> try { 
      tauto 
    } <;> try { 
      exfalso 
      <;> try { 
        tauto 
      } 
      <;> try { 
        omega 
      }
    }
  omega