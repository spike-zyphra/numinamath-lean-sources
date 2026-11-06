import Mathlib

def isSquareFriendly (c : ℤ) := ∀ m : ℤ, ∃ n : ℤ, n^2 = m^2 + 18 * m + c

theorem algebra_170476 :
    ∃! c : ℤ, isSquareFriendly c := by 
  use 81
  constructor
  · -- First show that 81 is square-friendly
    intro m
    use m + 9
    ring
  · -- Now, prove that if another c is square-friendly, then it must equal 81
    intro c hc
    have h1 := hc (-9)
    rcases h1 with ⟨n1, hn1⟩
    have h2 := hc (-8)
    rcases h2 with ⟨n2, hn2⟩
    have h3 := hc (-10)
    rcases h3 with ⟨n3, hn3⟩
    have h_eq1 : n1 ^ 2 = (-9) ^ 2 + 18 * (-9) + c := by linarith [hn1]
    have h_eq2 : n2 ^ 2 = (-8) ^ 2 + 18 * (-8) + c := by linarith [hn2]
    have h_eq3 : n3 ^ 2 = (-10) ^ 2 + 18 * (-10) + c := by linarith [hn3]
    have hc1 : c = n1 ^ 2 + 81 := by
      nlinarith
    have hc2 : c = n2 ^ 2 + 80 := by
      nlinarith
    have hc3 : c = n3 ^ 2 + 80 := by
      nlinarith
    have eq1 : n2 ^ 2 - n1 ^ 2 = 1 := by
      nlinarith [hc1, hc2]
    have eq2 : n3 ^ 2 - n1 ^ 2 = 1 := by
      nlinarith [hc1, hc3]
    have h4 : (n2 - n1) * (n2 + n1) = 1 := by
      nlinarith
    have h5 : n2 - n1 = 1 ∨ n2 - n1 = -1 := by
      have h6 : (n2 - n1) * (n2 + n1) = 1 := h4
      have h7 : n2 - n1 ∣ 1 := by
        use n2 + n1
        linarith
      have h8 : n2 - n1 = 1 ∨ n2 - n1 = -1 := by
        have h9 : n2 - n1 ≤ 1 := by
          apply Int.le_of_dvd (by norm_num) h7
        have h10 : n2 - n1 ≥ -1 := by
          have h11 : - (n2 - n1) ∣ 1 := by
            exact Int.neg_dvd.2 h7
          have h12 : - (n2 - n1) ≤ 1 := by
            apply Int.le_of_dvd (by norm_num) h11
          linarith
        interval_cases h : n2 - n1 <;> tauto
      tauto
    cases h5 with
    | inl h5 =>
      have h6 : n2 + n1 = 1 := by
        nlinarith
      have hn1_eq : n1 = 0 := by
        nlinarith
      have hc_eq : c = 81 := by
        nlinarith [hc1, hn1_eq]
      linarith
    | inr h5 =>
      have h6 : n2 + n1 = -1 := by
        nlinarith
      have hn1_eq : n1 = 0 := by
        nlinarith
      have hc_eq : c = 81 := by
        nlinarith [hc1, hn1_eq]
      linarith