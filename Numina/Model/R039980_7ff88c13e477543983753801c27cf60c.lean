import Mathlib

open Classical in
theorem algebra_17116 (Visible : ℕ → Prop) (visible_def : ∀ n, Visible n ↔ ∀ d ∈ Nat.digits 10 n, d ≠ 0 → d ∣ n) :
    ((Finset.Icc 100 150).filter Visible).card = 19 := by
  rw [Finset.filter]
  simp [Finset.Icc, visible_def]
  <;> try { native_decide }