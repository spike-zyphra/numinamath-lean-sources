import Mathlib

theorem algebra_199033 {a b : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∀ n, b n = (a n)^2) :
    ∃ d, ∀ n, b (n + 1) - b n = b 1 - b 0 + d * n := by 
  rcases ha with ⟨d, ha_eq⟩
  use 2 * d ^ 2 
  intro n

  have h1 : b (n + 1) = (a (n + 1) ) ^ 2 := by
    specialize hb (n + 1)
    simpa using hb
  have h2 : b n = (a n) ^ 2 := by
    specialize hb n
    simpa using hb 
  have eq1 : b (n + 1) - b n = (a (n + 1) ) ^ 2 - (a n) ^ 2 := by 
    rw [h1, h2]
    all_goals ring

  have eq2 : a (n + 1) = a n + d := by 
    have eq1 : a (n + 1) = a 0 + d * ((n + 1 : ℕ) : ℝ) := by
      specialize ha_eq (n + 1)
      simpa using ha_eq
    have eq2 : a n = a 0 + d * ((n : ℕ) : ℝ) := by 
      specialize ha_eq n 
      simpa using ha_eq 
    rw [eq1, eq2]
    simp at *
    <;> ring_nf 
  have eq3 : b (n + 1) - b n = 2 * a n * d + d ^ 2 := by 
    rw [eq1]
    have eq4 : (a (n + 1) ) ^ 2 - (a n) ^ 2 = 2 * a n * d + d ^ 2 := by 
      have eq5 : a (n + 1) = a n + d := eq2
      rw [eq5]
      nlinarith 
    linarith [eq4]

  have eq5 : b 1 - b 0 = 2 * a 0 * d + d ^ 2 := by 
    have h2_1 : b 1 = (a 1) ^ 2 := by 
      specialize hb 1 
      simpa using hb 
    have h2_2 : b 0 = (a 0) ^ 2 := by 
      specialize hb 0 
      simpa using hb 
    have h2_3 : a 1 = a 0 + d := by 
      specialize ha_eq 1 
      norm_num at ha_eq ⊢ 
      linarith 
    rw [h2_1, h2_2, h2_3]
    ring_nf

  have eq6 : b (n + 1) - b n = b 1 - b 0 + (2 * d ^ 2) * (n : ℝ) := by
    have eq7 : b (n + 1) - b n = 2 * a n * d + d ^ 2 := eq3 
    have eq8 : 2 * a n * d + d ^ 2 = b 1 - b 0 + (2 * d ^ 2) * (n : ℝ) := by 
      have ha_eq1 : a n = a 0 + d * ((n : ℕ) : ℝ) := by
        specialize ha_eq n 
        simpa using ha_eq
      have eq5' : b 1 - b 0 = 2 * a 0 * d + d ^ 2 := eq5 
      rw [eq5']
      rw [ha_eq1]
      ring_nf 
    linarith [eq7, eq8]

  simpa using eq6