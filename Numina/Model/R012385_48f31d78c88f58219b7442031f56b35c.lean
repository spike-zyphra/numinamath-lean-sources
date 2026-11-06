import Mathlib

theorem algebra_196116 {x p q r : ℝ} (hx : 0 < x) (hpqr : 0 < p ∧ p ≠ 1 ∧ 0 < q ∧ q ≠ 1 ∧ 0 < r ∧ r ≠ 1)
    (h₁ : Real.logb p x = 2) (h₂ : Real.logb q x = 3) (h₃ : Real.logb r x = 6) :
    Real.logb (p * q * r) x = 1 := by
  rcases hpqr with ⟨hp0, hhp1, hq0, hhq1, hr0, hhr1⟩
  have hp : Real.logb p x = Real.log x / Real.log p := by
    field_simp [Real.logb]
  have hq : Real.logb q x = Real.log x / Real.log q := by
    field_simp [Real.logb]
  have hr : Real.logb r x = Real.log x / Real.log r := by
    field_simp [Real.logb]
  have hpq : Real.logb (p * q * r) x = Real.log x / Real.log (p * q * r) := by
    field_simp [Real.logb]
  rw [hp] at h₁
  rw [hq] at h₂
  rw [hr] at h₃
  rw [hpq] at *
  have h4 : Real.log x = 2 * Real.log p := by 
    have hne : Real.log p ≠ 0 := by
      have hp0' : 0 < p := hp0
      have hp1' : p ≠ 1 := hhp1
      have : Real.log p ≠ 0 := by
        by_contra h
        have : p = 1 := by
          rw [Real.log_eq_zero] at h
          rcases h with (r | r | r)
          · linarith
          · linarith
          · linarith
        contradiction
      assumption
    field_simp at h₁ ⊢
    nlinarith
  have h5 : Real.log x = 3 * Real.log q := by 
    have hne : Real.log q ≠ 0 := by
      have hq0' : 0 < q := hq0
      have hq1' : q ≠ 1 := hhq1
      have : Real.log q ≠ 0 := by
        by_contra h
        have : q = 1 := by
          rw [Real.log_eq_zero] at h
          rcases h with (r | r | r)
          · linarith
          · linarith
          · linarith
        contradiction
      assumption
    field_simp at h₂ ⊢
    nlinarith
  have h6 : Real.log x = 6 * Real.log r := by 
    have hne : Real.log r ≠ 0 := by
      have hr0' : 0 < r := hr0
      have hr1' : r ≠ 1 := hhr1
      have : Real.log r ≠ 0 := by
        by_contra h
        have : r = 1 := by
          rw [Real.log_eq_zero] at h
          rcases h with (r | r | r)
          · linarith
          · linarith
          · linarith
        contradiction
      assumption
    field_simp at h₃ ⊢
    nlinarith
  have h7 : Real.log (p * q * r) = Real.log p + Real.log q + Real.log r := by
    simp [Real.log_mul, hp0.ne.symm, hq0.ne.symm, hr0.ne.symm]
  -- Express ln p and ln q in terms of ln x.
  have h8 : Real.log p = Real.log x / 2 := by
    linarith [h4]
  have h9 : Real.log q = Real.log x / 3 := by
    linarith [h5]
  have h10 : Real.log r = Real.log x / 6 := by
    linarith [h6]
  -- Substitute expressions for ln p, ln q, ln r in the expression for ln (p * q * r).
  have h11 : Real.log (p * q * r) = Real.log x := by
    rw [h7]
    rw [h8, h9, h10]
    linarith
  -- Obtain that x / x = 1.
  have hxne : Real.log x ≠ 0 := by
    by_contra h
    have h5' : Real.log x = 2 * Real.log p := by linarith [h4]
    have : Real.log p = 0 := by
      nlinarith
    have hp1 : p = 1 := by
      rw [Real.log_eq_zero] at this
      rcases this with (r | r | r)
      · linarith
      · linarith
      · linarith
    have hhp1' : p = 1 := hp1
    have hhp1'' : p ≠ 1 := hhp1
    contradiction
  rw [h11]
  field_simp [hxne]