import Mathlib

theorem number_theory_19001 {b : ℕ} (_ : 0 < b) (hb : Nat.digits b 57 = [1, 2, 3]) :
    b = 4 := by
  have h1 : 57 = 1 + b * (2 + b * 3) := by
    rw [← Nat.ofDigits_digits b 57, hb]
    simp [Nat.ofDigits]
  nlinarith [h1, show 1 ≤ b from by
    by_contra h
    push_neg at h
    omega]