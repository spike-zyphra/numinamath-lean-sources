import Mathlib

theorem algebra_5138 {k : ℝ} (P L : ℝ → ℝ)
    (hP : P = fun x => 2 * x ^ 2 + 19 * x + 35)
    (hL : L = fun x => 7 * x + k)
    (hP1 : ∃! x, P x = L x) :
    k = 17 := by
  rcases hP1 with ⟨x, h1, h2⟩
  have eq1 : 2 * x ^ 2 + 19 * x + 35 = 7 * x + k := by 
    rw [hP] at h1
    rw [hL] at h1
    simpa using h1
  have eq2 : 2 * x ^ 2 + 12 * x + (35 - k) = 0 := by 
    nlinarith 
  have h_eq1 : ∀ y : ℝ, 2 * y ^ 2 + 12 * y + (35 - k) = 0 → y = x := by 
    intro y hy 
    have h_eq2 : P y = L y := by 
      rw [hP, hL]
      simp
      nlinarith
    have h_eq3 : y = x := h2 y h_eq2
    exact h_eq3
  have h_eq2 : x = -3 := by 
    have eq3 := h_eq1 (-6 - x) (by 
      nlinarith [sq_nonneg (x + 3)]
    )
    nlinarith
  rw [h_eq2] at eq2
  nlinarith [sq_nonneg (k - 17)]