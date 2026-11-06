import Mathlib

/- What is the residue modulo $16$ of the sum of the modulo $16$ inverses of the first $8$ positive odd integers?

Express your answer as an integer from $0$ to $15$, inclusive. -/
theorem number_theory_23008 : ∑ i : (ZMod 16)ˣ, i.1⁻¹ = 0 := by
  -- $1^{-1} + 3^{-1} +...+ 15^{-1} = 1 + 3 +...+ 15$
  have eq : ∑ i : (ZMod 16)ˣ, i.1⁻¹ = ∑ i : (ZMod 16)ˣ, i.1 ^ 1 := by
    refine Fintype.sum_bijective (fun (x : (ZMod 16)ˣ) ↦ x⁻¹) (by exact Function.Involutive.bijective (congrFun rfl)) (fun x => (x.1)⁻¹) Units.val ?_
    intro x
    simp only [ZMod.inv_coe_unit]
  rw [eq]
  -- $1 + 3 +...+ 15 \equiv 0 \Mod{16}$
  exact rfl