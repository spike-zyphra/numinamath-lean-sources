import Mathlib

theorem algebra_978 {m n p : ℂ} (hn : n ≠ 0) (hp : p ≠ 0) (hm : m ≠ 0) (hmp : m + n - p = 0) :
    m * (1 / n - 1 / p) + n * (1 / m - 1 / p) - p * (1 / m + 1 / n) = -3 := by
  have hp_eq : p = m + n := by 
    have h1 : m + n = p := by 
      exact sub_eq_zero.1 hmp
    exact h1.symm

  have m_n_ne_zero : m + n ≠ 0 := by
    by_contra h'
    have hp_eq_zero : p = 0 := by
      rw [hp_eq]
      exact h'
    contradiction

  rw [hp_eq]
  field_simp [hm, hn, show m + n ≠ 0 by exact m_n_ne_zero, hp]
  <;> ring