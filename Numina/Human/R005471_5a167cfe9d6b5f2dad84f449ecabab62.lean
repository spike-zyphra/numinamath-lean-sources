import Mathlib

/-Alice rolls two octahedral dice with the numbers
2,3,4,5,6,7,8,9. What's the probability the two dice sum to 11 ?  -/

theorem combinatorics_608425 :
    ((Finset.Icc 2 9 ×ˢ Finset.Icc 2 9).filter (fun (x, y) => x + y = 11)).card /
    (Finset.Icc 2 9 ×ˢ Finset.Icc 2 9).card = (1: ℚ) / 8 := by

    suffices ((Finset.Icc 2 9 ×ˢ Finset.Icc 2 9).filter (fun (x, y) => x + y = 11)).card = 8
      ∧ (Finset.Icc 2 9 ×ˢ Finset.Icc 2 9).card = 64 by
        simp [this]
        norm_num
    refine ⟨(by native_decide), (by native_decide)⟩