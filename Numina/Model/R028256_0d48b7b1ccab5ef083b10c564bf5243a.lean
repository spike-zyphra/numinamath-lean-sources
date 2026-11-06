import Mathlib

theorem number_theory_75180 :
    IsLeast {n : ℕ | ∃ x y : ℤ, x ≠ y ∧ x^2 - n * x + 2014 = 0 ∧ y^2 - n * y + 2014 = 0} 91 := by
  constructor
  · -- Show that 91 is in the set, using x = 53 and y = 38.
    use 53, 38
    norm_num
  · -- Show that 91 is the smallest such natural number.
    intro n hn
    rcases hn with ⟨x, y, h1, h2, h3⟩
    by_contra h
    push_neg at h
    have h4 : n < 91 := by omega
    -- For all integer pairs (x, y) with x * y = 2014, if x + y < 91, then x = y
    have h4 : n < 91 := by omega
    have h5 : (x - y) * (x + y - (n : ℤ)) = 0 := by
      nlinarith
    have h6 : x - y ≠ 0 := by
      omega
    have h7 : x + y - (n : ℤ) = 0 := by
      apply_fun (fun z => z / (x - y)) at h5
      field_simp [show x - y ≠ 0 by omega] at h5
      linarith
    have h8 : (x + y : ℤ) = (n : ℤ) := by
      linarith
    have h9 : x * y = 2014 := by
      rw [show (n : ℤ) = x + y by linarith [h8]] at h2
      nlinarith
    have h10 : (x + y : ℤ) ≥ 0 := by
      omega
    have h11 : (x + y : ℤ) < 91 := by
      nlinarith [show (n : ℤ) < 91 from by exact_mod_cast h4]
    have h12 : x ≤ 90 := by
      nlinarith [show (x + y : ℤ) < 91 by omega, show x * y = 2014 by omega]
    have h13 : y ≤ 90 := by
      nlinarith [show (x + y : ℤ) < 91 by omega, show x * y = 2014 by omega]
    have h14 : x ≥ -90 := by
      nlinarith [show (x + y : ℤ) ≥ 0 by omega, show x * y = 2014 by omega]
    have h15 : y ≥ -90 := by
      nlinarith [show (x + y : ℤ) ≥ 0 by omega, show x * y = 2014 by omega]
    interval_cases x <;> omega