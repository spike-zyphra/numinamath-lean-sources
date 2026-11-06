import Mathlib

theorem number_theory_326540 (a b c : ℕ) (ha : a ∈ Finset.Icc 1000000 9999999)
    (hb : b ∈ Finset.Icc 1000000 9999999) (hc : c ∈ Finset.Icc 1000000 9999999)
    (h : a * b = 3 * c) :
    a = 1666667 ∧ b = 3333334 ∧ c = 500000 := by
  have h1 : a ≥ 1000000 := by
    simp [Finset.mem_Icc] at ha
    linarith
  have h2 : a ≤ 9999999 := by
    simp [Finset.mem_Icc] at ha
    linarith
  have h3 : b ≥ 1000000 := by
    simp [Finset.mem_Icc] at hb
    linarith
  have h4 : b ≤ 9999999 := by
    simp [Finset.mem_Icc] at hb
    linarith
  have h5 : c ≥ 1000000 := by
    simp [Finset.mem_Icc] at hc
    linarith
  have h6 : c ≤ 9999999 := by
    simp [Finset.mem_Icc] at hc
    linarith
  have h7 : a * b ≥ 1000000 * 1000000 := by
    nlinarith
  have h8 : 3 * c ≤ 3 * 9999999 := by
    nlinarith
  -- Lean will detect a contradiction since `a * b >= 1,000,000,000,000` and `3 * c <= 29,999,997`.
  -- Since `a * b = 3 * c`, this is impossible.
  have h9 : a * b ≤ 3 * c := by nlinarith
  have h10 : a * b ≥ 3 * c := by nlinarith
  have h11 : a * b = 3 * c := by linarith
  -- Lean should now detect that the constraints of a, b, c can't satisfy `a * b = 3 * c`.
  -- Therefore, the theorem is vacuously true.
  have h12 : False := by
    nlinarith
  exact False.elim h12