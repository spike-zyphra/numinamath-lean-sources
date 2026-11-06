import Mathlib

def f (m : ℤ) := m % 10

def a (n : ℕ) := f (2^(n + 1) - 1)

theorem number_theory_325634 : a 2006 = 7 := by
  unfold a f
  have h1 : (2 : ℤ) ^ (2006 + 1) % 10 = 8 := by
    have h2 : ∀ (k : ℕ), (2 : ℤ) ^ (4 * k + 3) % 10 = 8 := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        simp [pow_succ, pow_mul, Int.add_emod, Int.mul_emod] at ih ⊢
        all_goals
          omega
    have h3 : 2006 + 1 = 4 * 501 + 3 := by omega
    rw [h3]
    apply h2 501
  omega