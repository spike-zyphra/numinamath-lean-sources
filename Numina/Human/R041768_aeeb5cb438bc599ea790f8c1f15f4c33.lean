import Mathlib

/-let two strictly increasing sequences of positive integers an, bn satisfy: a10 = b10 < 2017, for any positive integer n, there is a (n+2) = a (n+1) + an, b(n+1)=2bn, 
then all possible values of a1 + b1 are -/

theorem number_theory_226154 (a b : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n ∧ 0 < b n)
    (h10 : a 10 = b 10 ∧ b 10 < 2017) (hadd : ∀ n, a (n + 2) = a (n + 1) + a n)
    (hmul : ∀ n, b (n + 1) = 2 * b n) :
    a 1 + b 1 = 13 ∨ a 1 + b 1 = 20 := by

-- first compute b10 
  have b10_eq : b 10 = 512 * b 1 := by
    have h1 := hmul 1
    have h2 := hmul 2
    have h3 := hmul 3
    have h4 := hmul 4
    have h5 := hmul 5
    have h6 := hmul 6
    have h7 := hmul 7
    have h8 := hmul 8
    have h9 := hmul 9
    norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9
    have hb1 : b 2 = 2 * b 1 := by linarith
    have hb2 : b 3 = 2 * b 2 := by linarith
    have hb3 : b 4 = 2 * b 3 := by linarith
    have hb4 : b 5 = 2 * b 4 := by linarith
    have hb5 : b 6 = 2 * b 5 := by linarith
    have hb6 : b 7 = 2 * b 6 := by linarith
    have hb7 : b 8 = 2 * b 7 := by linarith
    have hb8 : b 9 = 2 * b 8 := by linarith
    have hb9 : b 10 = 2 * b 9 := by linarith
    linarith [hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9]

-- then compute a10
  have a10_eq : a 10 = 21 * a 1 + 34 * a 2 := by
    have h1 := hadd 1
    have h2 := hadd 2
    have h3 := hadd 3
    have h4 := hadd 4
    have h5 := hadd 5
    have h6 := hadd 6
    have h7 := hadd 7
    have h8 := hadd 8
    have h9 := hadd 9
    norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9
    have ha1 : a 3 = a 2 + a 1 := by linarith
    have ha2 : a 4 = a 3 + a 2 := by linarith
    have ha3 : a 5 = a 4 + a 3 := by linarith
    have ha4 : a 6 = a 5 + a 4 := by linarith
    have ha5 : a 7 = a 6 + a 5 := by linarith
    have ha6 : a 8 = a 7 + a 6 := by linarith
    have ha7 : a 9 = a 8 + a 7 := by linarith
    have ha8 : a 10 = a 9 + a 8 := by linarith
    linarith [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]

  rcases h10 with ⟨h10_eq, h10_lt⟩
  rw [a10_eq] at h10_eq
  rw [b10_eq] at h10_eq

  have h1_pos : 0 < a 1 := (hpos 1).left
  have h2_pos : 0 < a 2 := (hpos 2).left
  have h1_lt_2 : a 1 < a 2 := by
    apply (ha (by norm_num : (1 : ℕ) < (2 : ℕ)))
  have h_b1_pos : 0 < b 1 := (hpos 1).right

-- from b10 < 2017, we can get b1 < 4
  have b1_cases : b 1 ≤ 3 := by
    nlinarith

  interval_cases b1 : b 1 <;> omega