import Mathlib
open Mathlib

theorem algebra_1189 (a b d base : ℝ) (hbase : 1 < base) (ha : 0 < a) (hb : 0 < b) (hb1 : b ≠ 1) (n : ℕ) (h1 : Real.logb base (a^5 * b^12) = Real.logb base (a^3 * b^7) + d) (h2 : Real.logb base (a^8 * b^15) = Real.logb base (a^3 * b^7) + 2 * d) (h3 : Real.logb base (b^n) = Real.logb base (a^3 * b^7) + 11 * d) : n = 112 := by
  have h1' : Real.logb base (a^5 * b^12) = 5 * Real.logb base a + 12 * Real.logb base b := by
    have h100 : Real.logb base (a^5 * b^12) = Real.logb base (a^5) + Real.logb base (b^12) := by 
      rw [Real.logb_mul (by positivity) (by positivity)]
    have h101 : Real.logb base (a^5) = 5 * Real.logb base a := by 
      simp [Real.logb_pow]
    have h102 : Real.logb base (b^12) = 12 * Real.logb base b := by 
      simp [Real.logb_pow]
    rw [h100, h101, h102]
  have h1'' : Real.logb base (a^3 * b^7) = 3 * Real.logb base a + 7 * Real.logb base b := by 
    have h110 : Real.logb base (a^3 * b^7) = Real.logb base (a^3) + Real.logb base (b^7) := by 
      rw [Real.logb_mul (by positivity) (by positivity)]
    have h111 : Real.logb base (a^3) = 3 * Real.logb base a := by 
      simp [Real.logb_pow]
    have h112 : Real.logb base (b^7) = 7 * Real.logb base b := by 
      simp [Real.logb_pow]
    rw [h110, h111, h112]
  have h1''' : Real.logb base (a^8 * b^15) = 8 * Real.logb base a + 15 * Real.logb base b := by
    have h120 : Real.logb base (a^8 * b^15) = Real.logb base (a^8) + Real.logb base (b^15) := by 
      rw [Real.logb_mul (by positivity) (by positivity)]
    have h121 : Real.logb base (a^8) = 8 * Real.logb base a := by 
      simp [Real.logb_pow]
    have h122 : Real.logb base (b^15) = 15 * Real.logb base b := by 
      simp [Real.logb_pow]
    rw [h120, h121, h122]
  have h4 : Real.logb base (b ^ n) = (n : ℝ) * Real.logb base b := by
    simp [Real.logb_pow]
  rw [h1'] at h1
  rw [h1''] at h1
  rw [h1'''] at h2
  rw [h1''] at h2
  rw [h4] at h3
  rw [h1''] at h3
  have h5 : Real.logb base a = 2 * Real.logb base b := by 
    nlinarith
  have h7 : (d : ℝ) = 9 * Real.logb base b := by
    nlinarith [h5]
  have h8 : (n : ℝ) * Real.logb base b = 112 * Real.logb base b := by 
    nlinarith [h5, h7]
  have h10 : Real.logb base b ≠ 0 := by
    by_contra h0
    have h9 : b = 1 := by
      have h30 : Real.logb base b = 0 := by linarith
      have h9 : b = (1 : ℝ) := by
        have h30' : Real.logb base b = 0 := h30
        have h9' : b = base ^ (0 : ℝ) := by
          rw [Real.logb_eq_iff_rpow_eq (by linarith) (by linarith) (by linarith)] at h30'
          · linarith
          all_goals linarith
        rw [h9'] 
        simp
        <;> linarith
      linarith
    tauto
  have h11 : (n : ℝ) = 112 := by
    apply (mul_left_inj' h10).mp 
    linarith
  have hn : n = 112 := by
    exact_mod_cast h11
  exact_mod_cast hn