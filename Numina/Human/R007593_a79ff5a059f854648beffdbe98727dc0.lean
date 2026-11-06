import Mathlib

/- Corollary 8.3 states that every prime number has at least one primitive root.-/
theorem number_theory_5014 (p : ℕ) [inst : Fact (Nat.Prime p)] : IsCyclic (ZMod p)ˣ := by
  --Construct the natural OneHom from the unit group to the ring ZMod p
  let UtoR : OneHom (ZMod p)ˣ (ZMod p) := OneHom.mk Units.val Units.val_one
  --Show that UtoR preserves multiplication
  have UtoRmul : ∀ (x y : (ZMod p)ˣ), UtoR.toFun (x * y) = UtoR.toFun x * UtoR.toFun y := Units.val_mul
  --Construct the MonoidHom from the unit group to the ring ZMod p
  let UtoRmor : (ZMod p)ˣ →* ZMod p := MonoidHom.mk UtoR UtoRmul
  --Show that UtoRmor is injective
  have : Function.Injective UtoRmor := by
    rw [Function.Injective]; intro x y; simp only [UtoRmor]; simp
    intro hxy; simp only [UtoR] at hxy; simp at hxy
    exact Units.eq_iff.mp hxy
  --Apply the lemma isCyclic_of_subgroup_isDomain and prove the result
  apply isCyclic_of_subgroup_isDomain UtoRmor this
