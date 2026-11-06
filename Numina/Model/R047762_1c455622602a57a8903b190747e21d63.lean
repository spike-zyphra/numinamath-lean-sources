import Mathlib

theorem number_theory_7069 (p : ℕ) (hp : Nat.Prime p) (a b : ℤ) :
    (a + b) ^ p ≡ a ^ p + b ^ p [ZMOD p] := by
  have h1 : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.int_cast_eq_int_cast_iff]
  simp [h1]