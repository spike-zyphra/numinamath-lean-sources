import Mathlib

theorem algebra_5638 {f : ℕ → ℕ → ℕ} (hf1 : ∀ n, f n 0 = n) (hf2 : ∀ n m, f n (m + 1) = f n m + n) :
    ∃! f : ℕ → ℕ → ℕ, (∀ n, f n 0 = n) ∧ (∀ n m, f n (m + 1) = f n m + n) := by
  exact ⟨f, by simp [hf1, hf2], fun g ⟨hg1, hg2⟩ => by
    funext n m
    induction m with
    | zero => simp [hf1 n, hg1 n]
    | succ m ih => simp [hf2 n m, hg2 n m, ih]⟩