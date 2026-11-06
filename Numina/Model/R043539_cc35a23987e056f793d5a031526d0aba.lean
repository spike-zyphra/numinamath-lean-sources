import Mathlib

theorem number_theory_198113 :
    Set.ncard {t : ℕ | t < 12 * 60 ∧ (t / 60) > t % 60} = 66 := by
  have : {t : ℕ | t < 12 * 60 ∧ (t / 60) > t % 60} = Finset.filter (fun t => (t / 60) > t % 60) (Finset.Iio (12 * 60)) := by
    ext t
    simp
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide