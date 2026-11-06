import Mathlib

theorem number_theory_44699 (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (h1 : 3 * a + 1 ∣ 4 * b - 1) (h2 : 2 * b + 1 ∣ 3 * a - 1) :
    (a, b) = (2, 2) := by
  rcases h1 with ⟨k, hk⟩
  rcases h2 with ⟨m, hm⟩
  have hk1 : k > 0 := by
    by_contra h
    push_neg at h
    have h0 : k ≤ 0 := by nlinarith
    have h1' : k < 1 := by nlinarith
    have h2' : k * (3 * a + 1) < 1 := by
      nlinarith
    have h3' : 4 * b - 1 < 1 := by
      nlinarith [hk, h2']
    have h4' : b < 1 := by
      omega
    omega
  have hm1 : m > 0 := by
    by_contra h
    push_neg at h
    have h0 : m ≤ 0 := by nlinarith
    have h1' : m < 1 := by nlinarith
    have h2' : m * (2 * b + 1) < 1 := by
      nlinarith
    have h3' : 3 * a - 1 < 1 := by
      nlinarith [hm, h2']
    have h4' : a < 1 := by
      omega
    omega
  have h1' : k = 1 := by
    by_cases h1 : k > 1
    · -- Assume k > 1
      have hk2 : k ≥ 2 := by omega
      have h4 : m < 2 := by
        nlinarith
      have hm2 : m = 1 := by
        omega
      rw [hm2] at hm
      nlinarith
    · -- Now k ≤ 1, so k = 1
      omega
  have h2' : m = 1 := by
    by_cases h2 : m > 1
    · -- Assume m > 1
      have hm2 : m ≥ 2 := by omega
      have h4 : k < 2 := by
        nlinarith
      have hk2 : k = 1 := by
        omega
      rw [hk2] at hk
      nlinarith
    · -- Now m ≤ 1, so m = 1
      omega
  have eq1 : 4 * b - 1 = k * (3 * a + 1) := by
    linarith [hk]
  rw [h1'] at eq1
  have eq2 : 3 * a - 1 = m * (2 * b + 1) := by
    linarith [hm]
  rw [h2'] at eq2
  have h3 : a = 2 := by
    omega
  have h4 : b = 2 := by
    omega
  exact Prod.ext h3 h4