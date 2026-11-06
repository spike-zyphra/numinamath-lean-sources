import Mathlib

theorem number_theory_4984 (a n : ℕ)(nzn : NeZero n) (han : Nat.Coprime a n) :
    orderOf (ZMod.unitOfCoprime a han) ∣ n.totient := by
  have h2 : orderOf (ZMod.unitOfCoprime a han) ∣ Fintype.card (ZMod n)ˣ := by 
    apply orderOf_dvd_card
  have h3 : Fintype.card (ZMod n)ˣ = n.totient := by
    simp
  rw [h3] at h2 
  exact h2