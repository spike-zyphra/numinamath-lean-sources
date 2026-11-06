import Mathlib

theorem number_theory_639469 (a b s : ℤ) (hb : 0 < b) :
    ∃! qr : ℤ × ℤ, a = b * qr.1 + qr.2 ∧ s ≤ qr.2 ∧ qr.2 < s + b := by 
  let r := (a - s) % b + s
  have aux1 : b ∣ a - ((a - s) % b + s) := by 
    have aux2 : a - ((a - s) % b + s) = a - s - ((a - s) % b) := by ring
    rw [aux2]
    exact Int.dvd_sub_of_emod_eq rfl
  obtain ⟨q, hq⟩ := aux1
  use ⟨q, r⟩
  simp
  constructor
  · 
    constructor
    · rw [←hq]
      unfold r
      ring
    constructor
    · 
      unfold r
      have pos : (a - s) % b ≥ 0 := by 
        refine Int.emod_nonneg (a - s) ?_
        linarith
      linarith
    · unfold r
      have ineq : (a - s) % b < b := by 
        exact Int.emod_lt_of_pos (a - s) hb
      linarith
  · 
    intro q2 r2 h1 h2 h3 
    have h4 : a = b * q + r := by 
      rw [←hq]
      unfold r
      ring
    have h5 : r ≥ s := by 
      unfold r
      have pos : (a - s) % b ≥ 0 := by 
        refine Int.emod_nonneg (a - s) ?_
        linarith
      linarith
    have h6 : r < s + b := by 
      unfold r
      have ineq : (a - s) % b < b := by 
        exact Int.emod_lt_of_pos (a - s) hb
      linarith
    have req : r2 = r := by 
      rw [h4] at h1
      have dvd1 : b * (q - q2) = r2 - r := by 
        linarith
      have bdvd : b ∣ r2 - r := by 
        rw [←dvd1]
        simp
      have absle : |r2 - r| < b := by 
        unfold abs
        simp
        constructor
        · linarith
        · linarith
      have aux1 : r2 - r = 0 := by 
        exact Int.eq_zero_of_abs_lt_dvd bdvd absle
      linarith
    rw [h4, req] at h1
    have aux2 : b * (q - q2) = 0 := by
      linarith
    have qeq : b = 0 ∨ q - q2 = 0 := by 
      exact Int.mul_eq_zero.mp aux2
    obtain h | h := qeq
    linarith
    have qeq2 : q2 = q := by 
      linarith
    exact ⟨qeq2, req⟩
