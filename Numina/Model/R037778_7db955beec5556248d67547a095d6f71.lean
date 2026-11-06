import Mathlib


open Int


lemma lemma_1 (w x y z : ℤ) (h₀ : w ≠ x) (h₁ : w ≠ y) (h₂ : w ≠ z)
    (h₃ : x ≠ y) (h₄ : x ≠ z) (h₅ : y ≠ z) (h₆ : w * x * y * z = 4) :
    w + x + y + z = 0 := by
  have h7 : w ≤ 4 := by
    have h8 : w ∣ 4 := by
      use x * y * z
      linarith
    have h7 : w ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h8
    linarith
  have h7a : w ≥ -4 := by
    have h8a : -w ∣ 4 := by
      exact Int.neg_dvd.2 (show w ∣ 4 by
        use x * y * z
        linarith
      )
    have h9 : -w ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h8a
    linarith
  have h8a : x ≤ 4 := by
    have h8 : x ∣ 4 := by
      use w * y * z
      linarith
    have h7 : x ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h8
    linarith
  have h8b : x ≥ -4 := by
    have h8a : -x ∣ 4 := by
      exact Int.neg_dvd.2 (show x ∣ 4 by
        use w * y * z
        linarith
      )
    have h9 : -x ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h8a
    linarith
  have h9 : y ≤ 4 := by
    have h8 : y ∣ 4 := by
      use w * x * z
      linarith
    have h7 : y ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h8
    linarith
  have h9a : y ≥ -4 := by
    have h8a : -y ∣ 4 := by
      exact Int.neg_dvd.2 (show y ∣ 4 by
        use w * x * z
        linarith
      )
    have h9 : -y ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h8a
    linarith
  have h10 : z ≤ 4 := by
    have h8 : z ∣ 4 := by
      use w * x * y
      linarith
    have h7 : z ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h8
    linarith
  have h10a : z ≥ -4 := by
    have h8a : -z ∣ 4 := by
      exact Int.neg_dvd.2 (show z ∣ 4 by
        use w * x * y
        linarith
      )
    have h9 : -z ≤ 4 := by
      apply Int.le_of_dvd (by norm_num) h8a
    linarith
  interval_cases w <;> interval_cases x <;> interval_cases y <;> omega


theorem algebra_125533 {a b c d k : ℤ} (hroots : {x | (x - a) * (x - b) * (x - c) * (x - d) = 0} = {a, b, c, d}) (hkroot : (k - a) * (k - b) * (k - c) * (k - d) = 4) (neqab : a ≠ b) (neqbc : b ≠ c) (neqcd : c ≠ d) (neqac : a ≠ c)(neqad : a ≠ d) (neqbd : b ≠ d):
    k = (a + b + c + d) / 4 := by

  have h13 : k - a ≠ k - b := by
    intro h
    have : a = b := by linarith
    tauto

  have h14 : k - a ≠ k - c := by
    intro h
    have : a = c := by linarith
    tauto

  have h15 : k - a ≠ k - d := by
    intro h
    have : a = d := by linarith
    tauto

  have h16 : k - b ≠ k - c := by
    intro h
    have : b = c := by linarith
    tauto

  have h17 : k - b ≠ k - d := by
    intro h
    have : b = d := by linarith
    tauto

  have h18 : k - c ≠ k - d := by
    intro h
    have : c = d := by linarith
    tauto

  have h19 : (k - a) + (k - b) + (k - c) + (k - d) = 0 := by
    have h20 : (k - a) * (k - b) * (k - c) * (k - d) = 4 := hkroot
    have h21 : (k - a) ≠ (k - b) := h13
    have h22 : (k - a) ≠ (k - c) := h14
    have h23 : (k - a) ≠ (k - d) := h15
    have h24 : (k - b) ≠ (k - c) := h16
    have h25 : (k - b) ≠ (k - d) := h17
    have h26 : (k - c) ≠ (k - d) := h18
    apply lemma_1 (k - a) (k - b) (k - c) (k - d) h21 h22 h23 h24 h25 h26 h20

  omega