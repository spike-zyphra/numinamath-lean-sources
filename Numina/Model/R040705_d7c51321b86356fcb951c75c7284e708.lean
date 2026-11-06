import Mathlib

theorem algebra_219403 (a : ℕ → ℕ) (ha : ∀ n, a n = 3 + 9 * n) :
    ∀ k, ∃ n, a n = 3 * 4 ^ k := by
  intro k; induction k with
  | zero => use 0; rw [ha]; simp
  | succ k ih =>
    rcases ih with ⟨n, hn⟩ 
    use n + 4 ^ k 
    have h1 : a (n + 4 ^ k) = 3 + 9 * (n + 4 ^ k) := by 
      apply ha 
    have h2 : 3 + 9 * n = 3 * 4 ^ k := by 
      specialize ha n 
      have h_eq : a n = 3 + 9 * n := ha 
      rw [h_eq] at hn 
      all_goals omega 
    calc 
      a (n + 4 ^ k) = 3 + 9 * (n + 4 ^ k) := by 
        apply ha 
      _ = 3 + 9 * n + 9 * 4 ^ k := by 
        ring 
      _ = (3 + 9 * n) + 9 * 4 ^ k := by 
        ring 
      _ = 3 * 4 ^ k + 9 * 4 ^ k := by 
        rw [h2]
      _ = 3 * 4 ^ (k + 1) := by 
        ring