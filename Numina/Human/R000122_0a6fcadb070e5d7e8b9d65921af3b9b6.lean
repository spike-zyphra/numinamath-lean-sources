import Mathlib

/-
Are there integers \( a, b, \) and \( c \) such that \( a \) divides \( b \cdot c \) (denoted as \( a \mid b c \)), but \( a \) does not divide \( b \) (denoted as \( a \nmid b \)) and \( a \) does not divide \( c \) (denoted as \( a \nmid c \))?
-/
theorem number_theory_4725 : ∃ (a b c : ℤ), a ∣ b * c ∧ ¬ a ∣ b ∧ ¬ a ∣ c := by
-- Solution:
-- We can notice that `a = 6`, `b = 2`, and `c = 3`, as we can check.
  use 6; use 2; use 3
  constructor
  · rfl
  · constructor
    · apply (Int.exists_lt_and_lt_iff_not_dvd 2 (show 0 < (6 : ℤ) by linarith)).mp
      use 0; aesop
    · apply (Int.exists_lt_and_lt_iff_not_dvd 3 (show 0 < (6 : ℤ) by linarith)).mp
      use 0; aesop
