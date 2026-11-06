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

/-A four-digit number, which itself is a perfect square,
is composed of two two-digit numbers, both of which are also perfect squares. What is this four-digit number? -/

theorem number_theory_139032 {n: ℕ} (hn: IsSquare n) (h: ∃ x y, 10 ≤ x ∧ x < 100 ∧
 IsSquare x ∧ 10 ≤ y ∧ y < 100 ∧ IsSquare y ∧ n = 100 * x + y): n = 1681 := by

  -- use lemma to give bound for x and y
  obtain ⟨x, y, lx, rx, sx, ly, ry, sy, h⟩ := h
  have tx: 16 ≤ x ∧ x ≤ 81 := by
    apply bound_of_two_digits_IsSquare
    exact ⟨lx, rx⟩
    exact sx
  have ty: 16 ≤ y ∧ y ≤ 81 := by
    apply bound_of_two_digits_IsSquare
    exact ⟨ly, ry⟩
    exact sy

  clear lx rx ly ry
  rcases tx with ⟨lx, rx⟩
  rcases ty with ⟨ly, ry⟩
  apply IsSquare.exists_sq at hn
  obtain ⟨k, hk⟩ := hn
  have lk: 40 < k := by nlinarith
  apply IsSquare.exists_sq at sx
  obtain ⟨a, ha⟩ := sx
  rw [ha] at h
  rw [show 100 * a ^ 2 = (10 * a) ^ 2 by ring] at h
  set u:= 10 * a
  rw [hk] at h
  have lu: u < k := by nlinarith
  replace lu: u ≤ k - 1 := by omega
  replace h: y = k ^ 2 - u ^ 2 := by omega

  -- then we give lower bound for y
  have ly: 2 * k - 1 ≤ y := by
    zify
    rw [show ↑(2 * k - 1) = 2 * k - (1: ℤ) by apply Int.natCast_sub; linarith]
    rw [h]
    rw [show ↑(k ^ 2 - u ^ 2) = (k ^ 2: ℤ) - u ^ 2 by apply Int.natCast_sub; omega]
    zify at lu
    rw [show ↑(k - 1) = (k: ℤ) - 1 by apply Int.natCast_sub; omega] at lu
    nlinarith
  have fy: 81 ≤ y := by omega

  -- hence y = 81, and k = 41
  have ey: y = 81 := by omega
  have ek: k ≤ 41 := by
    rw [ey] at ly
    omega
  have fk: k = 41 := by omega
  simp [fk] at hk
  exact hk
  