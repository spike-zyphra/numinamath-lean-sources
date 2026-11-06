import Mathlib

theorem number_theory_310930 (a b : ℕ) (ha : a = Nat.ofDigits 10 (List.replicate 1985 8)) (hb : b = Nat.ofDigits 10 (List.replicate 1985 5)) :
    (Nat.digits 10 (9 * a * b)).sum = 17865 := by
  rw [ha, hb]
  native_decide