import Mathlib

theorem number_theory_144625 : Set.ncard {x | ∃ y, x = y^9 % 999} = 15 := by
  have h1 : {x | ∃ y, x = y^9 % 999} = Finset.image (fun y => y^9 % 999) (Finset.Icc (0 : ℕ) 998) := by
    ext x
    simp
    constructor
    · -- Assume x is in the image
      rintro ⟨y, hy⟩
      have h2 : y^9 % 999 = (y % 999)^9 % 999 := by 
        rw [Nat.pow_mod, Nat.pow_mod]
      rw [h2] at hy
      use y % 999
      omega
    · -- Assume there exists y in [0, 998] such that x = y^9 % 999
      rintro ⟨y, hy, h2⟩
      use y
      simp [h2]
      all_goals omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide