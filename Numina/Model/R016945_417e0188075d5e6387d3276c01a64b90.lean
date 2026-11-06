import Mathlib

theorem algebra_277 {b c m n : ℝ} (h : ∃! x, x^2 + b * x + c = 0) (hA : m^2 + b * m + c = n)
    (hB : (m - 8)^2 + b * (m - 8) + c = n) : n = 16 := by
  rcases h with ⟨x, ⟨hx1, hx2⟩⟩
  have h1 : x ^ 2 + b * x + c = 0 := by
    simpa using hx1
  have h2 : ∀ y : ℝ, y ^ 2 + b * y + c = 0 → y = x := by
    intro y hy
    have hne := hx2 y hy
    tauto
  have h3 : (-b - x) ^ 2 + b * (-b - x) + c = 0 := by 
    nlinarith [h1]
  have h4 : (-b - x) = x := by
    apply h2 
    exact h3
  have h5 : x = -b / 2 := by 
    linarith 
  have h6 : c = b ^ 2 / 4 := by 
    rw [h5] at h1
    nlinarith 
  have eq1 : m ^ 2 + b * m + c = (m - 8) ^ 2 + b * (m - 8) + c := by
    linarith [hA, hB]
  have eq2 : m ^ 2 + b * m = (m - 8) ^ 2 + b * (m - 8) := by 
    linarith [eq1]
  have eq3 : 16 * m + 8 * b = 64 := by 
    ring_nf at eq2
    linarith 
  have eq4 : b = 8 - 2 * m := by 
    linarith 
  have h7 : c = (8 - 2 * m) ^ 2 / 4 := by 
    rw [show b = 8 - 2 * m by linarith [eq4] ] at h6
    linarith 
  -- From hA: n = m^2 + b*m + c, and b =8-2m, and c = (8-2m)^2/4.
  have h8 : n = m ^ 2 + (8 - 2 * m) * m + (8 - 2 * m) ^ 2 / 4 := by 
    rw [show b = 8 - 2 * m by linarith [eq4] ] at hA
    rw [show c = (8 - 2 * m) ^ 2 / 4 by linarith [h7] ] at hA
    linarith 
  nlinarith [h8]