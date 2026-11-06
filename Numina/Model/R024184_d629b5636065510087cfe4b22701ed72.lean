import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_312964 {a : ℕ → ℝ}
  (ha : ∀ n, a n = (cos (π/9))^n + (cos (5*π/9))^n + (cos (7*π/9))^n) :
  ∀ n, a (n+3) = 3/4 * a (n+1) + 1/8 * a n := by
  intro n
  have eq1 : a (n + 3) = (cos (π / 9)) ^ (n + 3) + (cos (5 * π / 9)) ^ (n + 3) + (cos (7 * π / 9)) ^ (n + 3) := by
    specialize ha (n + 3)
    simpa using ha

  have eq2 : a (n + 1) = (cos (π / 9)) ^ (n + 1) + (cos (5 * π / 9)) ^ (n + 1) + (cos (7 * π / 9)) ^ (n + 1) := by
    specialize ha (n + 1)
    simpa using ha

  have eq3 : a n = (cos (π / 9)) ^ n + (cos (5 * π / 9)) ^ n + (cos (7 * π / 9)) ^ n := by
    specialize ha n
    simpa using ha

  have h1 : 8 * (cos (π / 9)) ^ 3 - 6 * (cos (π / 9)) - 1 = 0 := by
    have h3 : cos (3 * (π / 9)) = 1 / 2 := by
      have h4 : 3 * (π / 9) = π / 3 := by ring
      rw [h4]
      exact Real.cos_pi_div_three
    have h6 : cos (3 * (π / 9)) = 4 * (cos (π / 9)) ^ 3 - 3 * (cos (π / 9)) := by
      rw [cos_three_mul]
    rw [h6] at h3
    nlinarith

  have h2 : 8 * (cos (5 * π / 9)) ^ 3 - 6 * (cos (5 * π / 9)) - 1 = 0 := by
    have h4 : cos (3 * (5 * π / 9)) = 1 / 2 := by
      have h5 : 3 * (5 * π / 9) = 5 * π / 3 := by ring
      rw [h5]
      have h6 : 5 * π / 3 = 2 * π - (π / 3) := by ring
      rw [h6]
      rw [cos_two_pi_sub]
      exact Real.cos_pi_div_three
    have h7 : cos (3 * (5 * π / 9)) = 4 * (cos (5 * π / 9)) ^ 3 - 3 * (cos (5 * π / 9)) := by
      rw [cos_three_mul]
    rw [h7] at h4
    nlinarith

  have h3 : 8 * (cos (7 * π / 9)) ^ 3 - 6 * (cos (7 * π / 9)) - 1 = 0 := by
    have h4 : cos (3 * (7 * π / 9)) = 1 / 2 := by
      have h5 : 3 * (7 * π / 9) = 7 * π / 3 := by ring
      rw [h5]
      have h6 : 7 * π / 3 = 2 * π + (π / 3) := by ring
      rw [h6]
      rw [cos_add, cos_two_pi, sin_two_pi]
      norm_num
      all_goals linarith [Real.cos_pi_div_three]
    have h7 : cos (3 * (7 * π / 9)) = 4 * (cos (7 * π / 9)) ^ 3 - 3 * (cos (7 * π / 9)) := by
      rw [cos_three_mul]
    rw [h7] at h4
    nlinarith

  have h1' : (cos (π / 9)) ^ 3 = (3 / 4) * (cos (π / 9)) + (1 / 8) := by
    nlinarith 
  have h2' : (cos (5 * π / 9)) ^ 3 = (3 / 4) * (cos (5 * π / 9)) + (1 / 8) := by 
    nlinarith
  have h3' : (cos (7 * π / 9)) ^ 3 = (3 / 4) * (cos (7 * π / 9)) + (1 / 8) := by
    nlinarith

  have eq4 : (cos (π / 9)) ^ (n + 3) = (3 / 4) * (cos (π / 9)) ^ (n + 1) + (1 / 8) * (cos (π / 9)) ^ n := by
    calc
      (cos (π / 9)) ^ (n + 3) = (cos (π / 9)) ^ n * ((cos (π / 9)) ^ 3) := by ring
      _ = (cos (π / 9)) ^ n * ((3 / 4) * (cos (π / 9)) + (1 / 8)) := by rw [h1']
      _ = (3 / 4) * (cos (π / 9)) ^ (n + 1) + (1 / 8) * (cos (π / 9)) ^ n := by ring

  have eq5 : (cos (5 * π / 9)) ^ (n + 3) = (3 / 4) * (cos (5 * π / 9)) ^ (n + 1) + (1 / 8) * (cos (5 * π / 9)) ^ n := by
    calc
      (cos (5 * π / 9)) ^ (n + 3) = (cos (5 * π / 9)) ^ n * ((cos (5 * π / 9)) ^ 3) := by ring
      _ = (cos (5 * π / 9)) ^ n * ((3 / 4) * (cos (5 * π / 9)) + (1 / 8)) := by rw [h2']
      _ = (3 / 4) * (cos (5 * π / 9)) ^ (n + 1) + (1 / 8) * (cos (5 * π / 9)) ^ n := by ring

  have eq6 : (cos (7 * π / 9)) ^ (n + 3) = (3 / 4) * (cos (7 * π / 9)) ^ (n + 1) + (1 / 8) * (cos (7 * π / 9)) ^ n := by
    calc
      (cos (7 * π / 9)) ^ (n + 3) = (cos (7 * π / 9)) ^ n * ((cos (7 * π / 9)) ^ 3) := by ring
      _ = (cos (7 * π / 9)) ^ n * ((3 / 4) * (cos (7 * π / 9)) + (1 / 8)) := by rw [h3']
      _ = (3 / 4) * (cos (7 * π / 9)) ^ (n + 1) + (1 / 8) * (cos (7 * π / 9)) ^ n := by ring
  
  have eq7 : a (n + 3) = (3 / 4) * a (n + 1) + (1 / 8) * a n := by 
    rw [eq1, eq2, eq3]
    rw [eq4, eq5, eq6]
    ring

  linarith