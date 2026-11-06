import Mathlib

/- Under what conditions is sqrt(a^2 + b^2) = a + b true, where a and b are real numbers?

(A) It is never true.
(B) It is true if and only if a*b = 0.
(C) It is true if and only if a + b ≥ 0.
(D) It is true if and only if a*b = 0 and a + b ≥ 0.
(E) It is always true. -/
theorem algebra_94114 (a b : ℝ) :
Real.sqrt (a ^ 2 + b ^ 2) = a + b ↔ a * b = 0 ∧ a + b ≥ 0 := by
  simp
  constructor <;> intro h
  ·
    -- square both sides
    have h2:= congr_arg (fun x=> x^2) h; simp at h2
    rw [Real.sq_sqrt (by
      apply add_nonneg; exact sq_nonneg a; exact sq_nonneg b
      )] at h2
    -- subtract a^2 + b^2 from both sides to get a*b = 0
    apply congr_arg (fun x=> x - a^2 - b^2) at h2
    ring_nf at h2
    simp at h2
    -- just basic logic
    exact ⟨h2, by
      linarith [Real.sqrt_nonneg (a^2 + b^2)]
    ⟩
  · obtain ⟨hl, hr⟩ := h
    cases' hl with hab hac
    -- since one of a or b is 0, we can just substitute and simplify
    · rw [hab]; simp
      rw [Real.sqrt_sq (by linarith)]
    · rw [hac]; simp
      rw [Real.sqrt_sq (by linarith)]