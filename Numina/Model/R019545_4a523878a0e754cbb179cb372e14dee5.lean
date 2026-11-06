import Mathlib

theorem number_theory_126365 (n : ℤ) :
    3 ∣ n^3 - n ∧
    5 ∣ n^5 - n ∧
    7 ∣ n^7 - n ∧
    11 ∣ n^11 - n ∧
    13 ∣ n^13 - n := by
  constructor
  · -- Show that $n^3 - n$ is divisible by 3
    have h1 : (n ^ 3 - n) % 3 = 0 := by
      have h1 : n^3 % 3 = n % 3 := by
        have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
          omega
        rcases h2 with (h2 | h2 | h2)
        · -- n % 3 = 0
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 3 = 1
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 3 = 2
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
      omega
    omega
  constructor
  · -- Show that $n^5 - n$ is divisible by 5
    have h1 : (n ^ 5 - n) % 5 = 0 := by
      have h2 : n^5 % 5 = n % 5 := by
        have h2 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
          omega
        rcases h2 with (h2 | h2 | h2 | h2 | h2)
        · -- n % 5 = 0
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 5 = 1
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 5 = 2
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 5 = 3
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 5 = 4
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
      omega
    omega
  constructor
  · -- Show that $n^7 - n$ is divisible by 7
    have h1 : (n ^ 7 - n) % 7 = 0 := by
      have h2 : n^7 % 7 = n % 7 := by
        have h2 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
          omega
        rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2)
        · -- n % 7 = 0
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 7 = 1
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 7 = 2
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 7 = 3
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 7 = 4
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 7 = 5
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 7 = 6
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
      omega
    omega
  constructor
  · -- Show that $n^{11} - n$ is divisible by 11
    have h1 : (n ^ 11 - n) % 11 = 0 := by
      have h2 : n^11 % 11 = n % 11 := by
        have h2 : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by
          omega
        rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2)
        · -- n % 11 = 0
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 11 = 1
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 11 = 2
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 11 = 3
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 11 = 4
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 11 = 5
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 11 = 6
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 11 = 7
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 11 = 8
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 11 = 9
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 11 = 10
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
      omega
    omega
  · -- Show that $n^{13} - n$ is divisible by 13
    have h1 : (n ^ 13 - n) % 13 = 0 := by
      have h2 : n^13 % 13 = n % 13 := by
        have h2 : n % 13 = 0 ∨ n % 13 = 1 ∨ n % 13 = 2 ∨ n % 13 = 3 ∨ n % 13 = 4 ∨ n % 13 = 5 ∨ n % 13 = 6 ∨ n % 13 = 7 ∨ n % 13 = 8 ∨ n % 13 = 9 ∨ n % 13 = 10 ∨ n % 13 = 11 ∨ n % 13 = 12 := by
          omega
        rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2)
        · -- n % 13 = 0
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 13 = 1
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 13 = 2
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 13 = 3
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 13 = 4
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 13 = 5
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 13 = 6
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 13 = 7
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 13 = 8
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 13 = 9
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 13 = 10
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 13 = 11
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
        · -- n % 13 = 12
          simp [h2, pow_succ, Int.add_emod, Int.mul_emod]
          <;> omega
      omega
    omega