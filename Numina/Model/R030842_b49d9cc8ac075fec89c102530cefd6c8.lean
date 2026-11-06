import Mathlib

open Nat Finset

theorem number_theory_95871 {n : ℕ} {d : ℕ →₀ ℕ}
    (hn : digits 5 n = [d 0, d 1, d 2, d 3, d 4])
    (h0 : ∀ i ∈ range 5, ∀ j ∈ range 5, d i = d j → i = j)
    (h1 : ofDigits 5 [d 0, d 1, d 4] + 1 = ofDigits 5 [d 2, d 1, d 4])
    (h2 : ofDigits 5 [d 2, d 1, d 4] + 1 = ofDigits 5 [d 3, d 4, d 4]) :
    ofDigits 5 [d 0, d 1, d 2] = 108 := by
  have eq1 : (d 0 : ℕ) + 1 = (d 2 : ℕ) := by
    simp [ofDigits, Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at h1 
    omega
  have eq2 : (d 2 : ℕ) + 1 + 5 * (d 1 : ℕ) = (d 3 : ℕ) + 5 * (d 4 : ℕ) := by
    simp [ofDigits, Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at h2 
    omega
  have h3 : (d 0 : ℕ) < 5 := by
    have h12 : (d 0 : ℕ) ∈ (digits 5 n) := by 
      rw [hn]
      simp
    exact Nat.digits_lt_base (by norm_num) h12
  have h4 : (d 1 : ℕ) < 5 := by 
    have h12 : (d 1 : ℕ) ∈ (digits 5 n) := by 
      rw [hn]
      simp
    exact Nat.digits_lt_base (by norm_num) h12
  have h5 : (d 2 : ℕ) < 5 := by 
    have h12 : (d 2 : ℕ) ∈ (digits 5 n) := by 
      rw [hn]
      simp
    exact Nat.digits_lt_base (by norm_num) h12
  have h6 : (d 3 : ℕ) < 5 := by 
    have h12 : (d 3 : ℕ) ∈ (digits 5 n) := by 
      rw [hn]
      simp
    exact Nat.digits_lt_base (by norm_num) h12
  have h7 : (d 4 : ℕ) < 5 := by 
    have h12 : (d 4 : ℕ) ∈ (digits 5 n) := by 
      rw [hn]
      simp
    exact Nat.digits_lt_base (by norm_num) h12
  have h8 : (d 0 : ℕ) ≠ (d 1 : ℕ) := by
    intro h
    have h9 : (0 : ℕ) = (1 : ℕ) := by 
      have h10 : d 0 = d 1 := by 
        simpa using h
      have h11 : (0 : ℕ) = (1 : ℕ) := by
        apply h0 0 (by simp) 1 (by simp) h10
      linarith
    omega
  have h9 : (d 0 : ℕ) ≠ (d 2 : ℕ) := by
    intro h
    have h10 : (0 : ℕ) = (2 : ℕ) := by 
      have h11 : d 0 = d 2 := by 
        simpa using h
      have h12 : (0 : ℕ) = (2 : ℕ) := by
        apply h0 0 (by simp) 2 (by simp) h11
      linarith
    omega
  have h10 : (d 1 : ℕ) ≠ (d 2 : ℕ) := by
    intro h
    have h11 : (1 : ℕ) = (2 : ℕ) := by 
      have h12 : d 1 = d 2 := by 
        simpa using h
      have h13 : (1 : ℕ) = (2 : ℕ) := by
        apply h0 1 (by simp) 2 (by simp) h12
      linarith
    omega
  have h11 : (d 0 : ℕ) ≠ (d 3 : ℕ) := by
    intro h
    have h12 : (0 : ℕ) = (3 : ℕ) := by 
      have h13 : d 0 = d 3 := by 
        simpa using h
      have h14 : (0 : ℕ) = (3 : ℕ) := by
        apply h0 0 (by simp) 3 (by simp) h13
      linarith
    omega
  have h12 : (d 1 : ℕ) ≠ (d 3 : ℕ) := by
    intro h
    have h13 : (1 : ℕ) = (3 : ℕ) := by 
      have h14 : d 1 = d 3 := by 
        simpa using h
      have h15 : (1 : ℕ) = (3 : ℕ) := by
        apply h0 1 (by simp) 3 (by simp) h14
      linarith
    omega
  have h13 : (d 2 : ℕ) ≠ (d 3 : ℕ) := by
    intro h
    have h14 : (2 : ℕ) = (3 : ℕ) := by 
      have h15 : d 2 = d 3 := by 
        simpa using h
      have h16 : (2 : ℕ) = (3 : ℕ) := by
        apply h0 2 (by simp) 3 (by simp) h15
      linarith
    omega
  have h14 : (d 0 : ℕ) ≠ (d 4 : ℕ) := by
    intro h
    have h15 : (0 : ℕ) = (4 : ℕ) := by 
      have h16 : d 0 = d 4 := by 
        simpa using h
      have h17 : (0 : ℕ) = (4 : ℕ) := by
        apply h0 0 (by simp) 4 (by simp) h16
      linarith
    omega
  have h15 : (d 1 : ℕ) ≠ (d 4 : ℕ) := by
    intro h
    have h16 : (1 : ℕ) = (4 : ℕ) := by 
      have h17 : d 1 = d 4 := by 
        simpa using h
      have h18 : (1 : ℕ) = (4 : ℕ) := by
        apply h0 1 (by simp) 4 (by simp) h17
      linarith
    omega
  have h16 : (d 2 : ℕ) ≠ (d 4 : ℕ) := by
    intro h
    have h17 : (2 : ℕ) = (4 : ℕ) := by 
      have h18 : d 2 = d 4 := by 
        simpa using h
      have h19 : (2 : ℕ) = (4 : ℕ) := by
        apply h0 2 (by simp) 4 (by simp) h18
      linarith
    omega
  have h17 : (d 3 : ℕ) ≠ (d 4 : ℕ) := by
    intro h
    have h18 : (3 : ℕ) = (4 : ℕ) := by 
      have h19 : d 3 = d 4 := by 
        simpa using h
      have h20 : (3 : ℕ) = (4 : ℕ) := by
        apply h0 3 (by simp) 4 (by simp) h19
      linarith
    omega
  simp [ofDigits, Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at *
  omega