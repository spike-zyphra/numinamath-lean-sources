import Mathlib

theorem algebra_216555 (M : Finset ℕ) (hM : M = Finset.Icc 1 1993)
    (f : ℕ → ℕ → ℕ) (hf : ∀ a b, f a b ∈ M) (h : ∀ a b, f (f a b) a = b) :
    ∃ a, f a a = a := by
  have h1 := h 0 0
  have h2 : f 0 0 ∈ M := hf 0 0
  rw [hM] at h2
  simp at h2
  have h6 : f (f 0 0) 0 ∈ M := hf (f 0 0) 0
  rw [h1] at h6
  rw [hM] at h6
  simp at h6
  all_goals omega