import Mathlib

theorem algebra_274133
  {a b c : ℝ} (hsum : a + b + c = 0) (hprod : a * b * c = 1) :
  ((a > 0) ∧ (b < 0) ∧ (c < 0)) ∨
  ((b > 0) ∧ (a < 0) ∧ (c < 0)) ∨
  ((c > 0) ∧ (a < 0) ∧ (b < 0)) := by
  have not_zero : a ≠ 0 ∧ b ≠ 0  ∧ c ≠ 0  := by 
    by_contra hc
    have aux : a = 0 ∨ b = 0 ∨ c = 0 := by 
      by_contra ha
      simp at ha
      tauto
    simp at hc
    obtain h1 | h2 | h3 := aux
    rw [h1] at hprod; simp at hprod
    rw [h2] at hprod; simp at hprod
    rw [h3] at hprod; simp at hprod
  have exist_neg : a < 0 ∨ b < 0 ∨ c < 0 := by 
    by_contra hc
    simp at hc
    obtain ⟨h1, h2, h3⟩ := hc
    obtain ⟨h1', h2', h3'⟩ := not_zero
    have agt : a > 0 := by 
      exact lt_of_le_of_ne h1 (id (Ne.symm h1'))
    have aux : a + b + c > 0 := by nlinarith
    rw [hsum] at aux
    linarith
  obtain ha | hb | hc := exist_neg
  have negbc : b < 0 ∨ c < 0 := by 
    by_contra hc
    simp at hc
    obtain ⟨hc1, hc2⟩ := hc
    have neg_aux : a * b * c ≤ 0 := by 
      have bc_pos : b * c ≥ 0 := by nlinarith
      have eq_aux : a * b * c= a * (b * c) := by 
        ring
      rw [eq_aux]
      nlinarith
    rw [hprod] at neg_aux
    linarith
  obtain h1 | h2 := negbc
  right; right
  constructor
  linarith
  constructor; simpa; simpa
  right; left
  constructor; linarith
  exact ⟨ha, h2⟩
  have negac : a < 0 ∨ c < 0 := by
    by_contra hc
    simp at hc
    obtain ⟨hc1, hc2⟩ := hc
    have neg_aux : a * b * c ≤ 0 := by 
      have bc_pos : a * c ≥ 0 := by nlinarith
      have eq_aux : a * b * c= a * (b * c) := by 
        ring
      rw [eq_aux]
      nlinarith
    rw [hprod] at neg_aux
    linarith
  obtain h1 | h2 := negac
  right; right
  constructor
  linarith
  constructor; simpa; simpa
  left
  constructor; linarith
  exact ⟨hb, h2⟩
  have negab : a < 0 ∨ b < 0 := by
    by_contra hc
    simp at hc
    obtain ⟨hc1, hc2⟩ := hc
    have neg_aux : a * b * c ≤ 0 := by 
      have bc_pos : a * b ≥ 0 := by nlinarith
      have eq_aux : a * b * c= a * (b * c) := by 
        ring
      rw [eq_aux]
      nlinarith
    rw [hprod] at neg_aux
    linarith
  obtain h1 | h2 := negab
  right; left
  constructor
  linarith
  constructor; simpa; simpa
  left
  constructor; linarith
  exact ⟨h2, hc⟩