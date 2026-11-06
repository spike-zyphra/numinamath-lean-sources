import Mathlib

theorem number_theory_624683 (n : ℤ) (a1 a2 a3 a4 a5 a6 a7 a8 : ℤ)
(hn: n = a8 * 10^7 + a7 * 10^6 + a6 * 10^5 + a5 * 10^4 + a4 * 10^3 + a3 * 10^2 + a2 * 10^1 + a1)
(l1: 0 ≤ a1 ∧ a1 ≤ 9) (l4: 0 ≤ a4 ∧ a4 ≤ 9) (l8: 1 ≤ a8 ∧ a8 ≤ 9)
(h1: a8 = a7) (h2: a7 = a6) (h3: a6 = a5)
(h4: (a4 = a5 + 1 ∧ a3 = a4 + 1 ∧ a2 = a3 + 1 ∧ a1 = a2 + 1) ∨ (a4 = a5 - 1 ∧ a3 = a4 - 1 ∧ a2 = a3 - 1 ∧ a1 = a2 - 1))
(h5: a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 = a2 * 10 + a1): n = 88887654 := by
  rcases l1 with ⟨h11, h12⟩
  rcases l4 with ⟨h41, h42⟩
  rcases l8 with ⟨h81, h82⟩
  rcases h4 with (h | h)
  · -- Assume first case of h4: the digits $a_1, a_2, a_3, a_4, a_5$ form a decreasing sequence.
    rcases h with ⟨ha4, ha3, ha2, ha1⟩
    have ha5 : a4 = a5 + 1 := by linarith
    have ha6 : a3 = a5 + 2 := by
      linarith
    have ha7 : a2 = a5 + 3 := by
      linarith
    have ha8 : a1 = a5 + 4 := by
      linarith
    have ha6' : a6 = a5 := by
      linarith [h1, h2, h3]
    have ha7' : a7 = a5 := by
      linarith [h1, h2, h3]
    have ha8' : a8 = a5 := by
      linarith [h1, h2, h3]
    omega
  · -- Assume second case of h4: the digits $a_1, a_2, a_3, a_4, a_5$ form an increasing sequence.
    rcases h with ⟨ha4, ha3, ha2, ha1⟩
    have ha5 : a4 = a5 - 1 := by linarith
    have ha6 : a3 = a5 - 2 := by
      linarith
    have ha7 : a2 = a5 - 3 := by
      linarith
    have ha8 : a1 = a5 - 4 := by
      linarith
    have ha6' : a6 = a5 := by
      linarith [h1, h2, h3]
    have ha7' : a7 = a5 := by
      linarith [h1, h2, h3]
    have ha8' : a8 = a5 := by
      linarith [h1, h2, h3]
    have ha51 : a5 = 8 := by
      omega
    have ha1 : a1 = 4 := by
      linarith 
    have ha2 : a2 = 5 := by
      linarith 
    have ha3 : a3 = 6 := by
      linarith 
    have ha4 : a4 = 7 := by
      linarith 
    have ha5 : a5 = 8 := by 
      linarith 
    have ha6 : a6 = 8 := by
      linarith [h1, h2, h3, ha5] 
    have ha7 : a7 = 8 := by 
      linarith [h1, h2, h3, ha5] 
    have ha8 : a8 = 8 := by 
      linarith [h1, h2, h3, ha5]
    norm_num [hn, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8] at *