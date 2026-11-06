import Mathlib

  theorem number_theory_250350 : (2^40 : ℕ) < 3^28 ∧ 31^11 < 17^14 := by
    constructor
    · -- Prove $2^{40} < 3^{28}$
      norm_num
    · -- Prove $31^11 < 17^14$
      norm_num