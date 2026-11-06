import Mathlib

def is_prime (n : ℕ) : Prop := n.Prime

theorem number_theory_282990 : is_prime 23 := by 
  unfold is_prime
  norm_num