import Mathlib

theorem algebra_21556 (s : Finset (ℕ × ℕ × ℕ)) (hs : s = ((Finset.Icc 1 12) ×ˢ (Finset.Icc 1 12) ×ˢ
      (Finset.Icc 1 12)).filter fun ⟨a, b, c⟩ => b ≠ c) :
    s.card = 1584 := by 
  rw [hs]
  native_decide