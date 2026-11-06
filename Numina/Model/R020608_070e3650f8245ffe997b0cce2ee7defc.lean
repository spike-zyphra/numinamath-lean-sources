import Mathlib

theorem algebra_310851 {a b : ℕ → ℝ} (ha : ∀ n, a n = 1 * 2 ^ n) (hb : ∀ n, b n = 2 + 5 * n)
    (x : ℕ → ℝ) (hx : ∀ n, ∃ m, a n = b m ∧ x n = a n) :
    x 100 = 2 ^ 397 := by
  have h1 : ∀ n, a n = 1 * 2 ^ n := ha
  have h2 : ∀ n, b n = 2 + 5 * n := hb

  have eq0 := hx 0
  rcases eq0 with ⟨m0, eq1, eq2⟩

  have eq1' : a 0 = b m0 := eq1
  have eq2' : x 0 = a 0 := eq2

  have ha0 : a 0 = 1 := by
    rw [h1 0]
    norm_num

  have hb0 : b m0 = 2 + 5 * (m0 : ℝ) := by
    simpa [h2] using h2 m0

  rw [ha0] at eq1'
  rw [hb0] at eq1'
  have eq3 : (1 : ℝ) = 2 + 5 * (m0 : ℝ) := by
    linarith 
  have eq4 : (m0 : ℝ) ≥ 0 := by
    exact_mod_cast show (m0 : ℕ) ≥ 0 by omega
  nlinarith