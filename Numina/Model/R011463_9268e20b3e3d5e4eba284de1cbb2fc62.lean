import Mathlib

lemma bound_of_two_digits_IsSquare {m: ℕ} (hm: 10 ≤ m ∧ m < 100) (s: IsSquare m): 16 ≤ m ∧ m ≤ 81 := by
  apply IsSquare.exists_sq at s
  obtain ⟨k, hk⟩ := s
  simp [hk] at hm
  rcases hm with ⟨l, r⟩
  simp [hk]
  constructor
  .
    replace l: 3 < k := by nlinarith
    replace l: 4 ≤ k := by omega
    nlinarith
  .
    replace r: k < 10 := by nlinarith
    replace r: k ≤ 9 := by omega
    nlinarith

theorem number_theory_139032 {n: ℕ} (hn: IsSquare n) (h: ∃ x y, 10 ≤ x ∧ x < 100 ∧
 IsSquare x ∧ 10 ≤ y ∧ y < 100 ∧ IsSquare y ∧ n = 100 * x + y): n = 1681 := by
  rcases h with ⟨x, y, hx1, hx2, hsqx, hy1, hy2, hsqy, heq⟩
  have h1 : 16 ≤ x := (bound_of_two_digits_IsSquare ⟨hx1, hx2⟩ hsqx).1
  have h2 : 16 ≤ y := (bound_of_two_digits_IsSquare ⟨hy1, hy2⟩ hsqy).1
  have h3 : x ≤ 81 := (bound_of_two_digits_IsSquare ⟨hx1, hx2⟩ hsqx).2
  have h4 : y ≤ 81 := (bound_of_two_digits_IsSquare ⟨hy1, hy2⟩ hsqy).2
  rcases hsqx with ⟨a, ha⟩ 
  rcases hsqy with ⟨b, hb⟩ 
  have h5 : a ≤ 9 := by nlinarith [sq_nonneg (a : ℕ), ha, h3]
  have h6 : b ≤ 9 := by nlinarith [sq_nonneg (b : ℕ), hb, h4]
  have h7 : a ≥ 4 := by nlinarith [sq_nonneg (a : ℕ), ha, h1]
  have h8 : b ≥ 4 := by nlinarith [sq_nonneg (b : ℕ), hb, h2]
  rcases hn with ⟨r, hr⟩
  have h_eq : r ^ 2 = 100 * (a ^ 2) + b ^ 2 := by
    have h_eq1 : n = r ^ 2 := by linarith [hr]
    rw [h_eq1] at heq
    rw [show x = a ^ 2 by linarith [ha] ] at heq
    rw [show y = b ^ 2 by linarith [hb] ] at heq 
    nlinarith
  have h9 : r ≤ 90 := by
    nlinarith [sq_nonneg (r : ℕ), h_eq]
  have h10 : r ≥ 41 := by
    nlinarith [sq_nonneg (r : ℕ), h_eq]
  interval_cases a <;> interval_cases b 
  <;> 
    try { 
      norm_num at h_eq
      interval_cases r <;> omega
    }