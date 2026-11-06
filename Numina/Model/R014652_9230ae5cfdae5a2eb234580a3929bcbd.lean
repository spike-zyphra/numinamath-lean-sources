import Mathlib

theorem number_theory_237814 (d r : ℤ) (h₀ : d > 1) (h₁ : 1059 % d = r) (h₂ : 1417 % d = r)
    (h₃ : 2312 % d = r) :
    d - r = 15 := by

  have h4 : d ∣ 358 := by
    have h5 : (1417 : ℤ) % d = r := h₂
    have h6 : (1059 : ℤ) % d = r := h₁
    have h7 : (1417 : ℤ) % d = (1059 : ℤ) % d := by
      rw [h5, h6]
    have h8 : d ∣ (1417 : ℤ) - (1059 : ℤ) := by
      exact Int.dvd_of_emod_eq_zero (by
        rw [Int.sub_emod]
        rw [h7]
        all_goals
          simp
      )
    have h9 : (1417 : ℤ) - (1059 : ℤ) = (358 : ℤ) := by
      norm_num
    rw [h9] at h8
    exact h8

  have h10 : d ∣ 895 := by
    have h11 : (2312 : ℤ) % d = r := h₃
    have h12 : (1417 : ℤ) % d = r := h₂
    have h13 : (2312 : ℤ) % d = (1417 : ℤ) % d := by
      rw [h11, h12]
    have h14 : d ∣ (2312 : ℤ) - (1417 : ℤ) := by
      exact Int.dvd_of_emod_eq_zero (by
        rw [Int.sub_emod]
        rw [h13]
        all_goals
          simp
      )
    have h15 : (2312 : ℤ) - (1417 : ℤ) = (895 : ℤ) := by
      norm_num
    rw [h15] at h14
    exact h14

  have h16 : d ∣ 1253 := by
    have h17 : (2312 : ℤ) % d = r := h₃
    have h18 : (1059 : ℤ) % d = r := h₁
    have h19 : (2312 : ℤ) % d = (1059 : ℤ) % d := by
      rw [h17, h18]
    have h20 : d ∣ (2312 : ℤ) - (1059 : ℤ) := by
      exact Int.dvd_of_emod_eq_zero (by
        rw [Int.sub_emod]
        rw [h19]
        all_goals
          simp
      )
    have h21 : (2312 : ℤ) - (1059 : ℤ) = (1253 : ℤ) := by
      norm_num
    rw [h21] at h20
    exact h20

  have h100 : d ∣ 179 := by
    exact Int.dvd_gcd (Int.dvd_gcd h4 h10) h16

  have h101 : d ≤ 179 := by
    exact Int.le_of_dvd (show (0 : ℤ) < 179 by norm_num) h100

  have h104 : d = 179 := by
    have h106 : d ≥ 2 := by
      omega
    have h105 : d ≤ 179 := h101
    interval_cases d <;> norm_num at h100 h₁ h₂ h₃ ⊢
    <;> omega

  have h107 : d = 179 := h104
  have h108 : r = 164 := by
    rw [h107] at h₁
    omega

  rw [h107, h108]
  all_goals
    norm_num