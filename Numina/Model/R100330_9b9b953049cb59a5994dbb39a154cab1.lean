import Mathlib

theorem number_theory_111718 (a b c : ℕ) (_ : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : Nat.gcd a c = Nat.gcd b c) (h2 : Nat.lcm a c = Nat.lcm b c) :
    a = b := by
  have h3 : a.gcd c * a.lcm c = a * c := by 
    rw [Nat.gcd_mul_lcm]
  have h4 : b.gcd c * b.lcm c = b * c := by 
    rw [Nat.gcd_mul_lcm]
  have h5 : a.gcd c = b.gcd c := h1
  have h6 : a.lcm c = b.lcm c := h2

  rw [h5, h6] at h3
  have h7 : a * c = b * c := by 
    linarith [h3, h4]
  have h8 : a = b := by
    apply (mul_left_inj' hc).mp
    linarith
  exact h8