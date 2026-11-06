import Mathlib

theorem number_theory_5014 (p : ℕ) [inst : Fact (Nat.Prime p)] : IsCyclic (ZMod p)ˣ := by 
  infer_instance