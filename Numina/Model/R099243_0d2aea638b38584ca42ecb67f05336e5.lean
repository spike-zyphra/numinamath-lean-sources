import Mathlib

theorem number_theory_3646 (p d : ℕ) [inst : Fact (Nat.Prime p)] (hd : 0 < d)
    (h : Set.ncard {x : (ZMod p)ˣ | x ^ d = 1} ≤ d) :
    IsCyclic ((ZMod p)ˣ) := by 
  infer_instance