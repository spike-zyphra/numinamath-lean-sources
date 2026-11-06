import Mathlib

theorem algebra_54056 {n : ℕ} (hn : 2 ≤ n) (R : Type*) [CommRing R]
    (I : Fin n → Ideal R) (h : ∀ H : Finset (Fin n), H ≠ ∅ →
    ∃ J : Ideal R, ∑ h ∈ H, I h = J) :
    ∃ K : Ideal R, ∑ i : Fin n, (∏ j : Fin n, if j ≠ i then I j else 1) = K := by
  refine' ⟨∑ i : Fin n, (∏ j : Fin n, if j ≠ i then I j else 1), rfl⟩