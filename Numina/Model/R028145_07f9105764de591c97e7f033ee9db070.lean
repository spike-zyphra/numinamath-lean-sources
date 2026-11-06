import Mathlib

theorem number_theory_287147 (a b c : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (h : (a * b * c) / 13 = (a * b * c) / 12 + 12) :
    2 * (a * b + b * c + c * a) = 142 := by
  have ha2 : a ≥ 2 := by linarith 
  have hb2 : b ≥ 2 := by linarith 
  have hc2 : c ≥ 2 := by linarith 
  have h4 : a ≤ 13 := by 
    by_contra h4
    push_neg at h4 
    have ha14 : a ≥ 14 := by omega 
    have h14 : a * b * c ≥ 14 * (b * c) := by 
      have h6 : b ≥ 2 := by omega
      have h7 : c ≥ 2 := by omega 
      nlinarith [show b * c > 0 by nlinarith] 
    have h8 : (a * b * c) / 13 > (a * b * c) / 12 := by 
      have h10 : (a * b * c) > (13 * (b * c)) := by
        nlinarith [show b * c > 0 by nlinarith]
      have h14 : (a * b * c) / 12 < (a * b * c) / 13 := by 
        omega 
      omega 
    omega 
  have h5 : b ≤ 13 := by 
    by_contra h4
    push_neg at h4 
    have hb14 : b ≥ 14 := by omega 
    have h14 : a * b * c ≥ 14 * (a * c) := by 
      have h6 : a ≥ 2 := by omega 
      have h7 : c ≥ 2 := by omega 
      nlinarith [show a * c > 0 by nlinarith]
    have h8 : (a * b * c) / 13 > (a * b * c) / 12 := by 
      have h10 : (a * b * c) > (13 * (a * c)) := by
        nlinarith [show a * c > 0 by nlinarith]
      have h14 : (a * b * c) / 12 < (a * b * c) / 13 := by 
        omega 
      omega 
    omega 
  have h6 : c ≤ 13 := by 
    by_contra h5 
    push_neg at h5 
    have hc14 : c ≥ 14 := by omega 
    have h14 : a * b * c ≥ 14 * (a * b) := by 
      have h6 : a ≥ 2 := by omega 
      have h7 : b ≥ 2 := by omega 
      nlinarith [show a * b > 0 by nlinarith]
    have h8 : (a * b * c) / 13 > (a * b * c) / 12 := by 
      have h10 : (a * b * c) > (13 * (a * b)) := by
        nlinarith [show a * b > 0 by nlinarith]
      have h14 : (a * b * c) / 12 < (a * b * c) / 13 := by 
        omega
      omega 
    omega 
  interval_cases a <;> interval_cases b <;> interval_cases c 
  <;> omega