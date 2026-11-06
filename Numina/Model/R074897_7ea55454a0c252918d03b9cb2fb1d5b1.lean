import Mathlib

theorem number_theory_97964 (Samantha_age : ℕ) (hSamantha_age : Samantha_age = 12) :
    (1985 + 6) = 1979 + Samantha_age := by 
  calc
    1985 + 6 = 1979 + 12 := by norm_num
    _ = 1979 + Samantha_age := by rw [hSamantha_age]