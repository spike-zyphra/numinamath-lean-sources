import Mathlib

theorem number_theory_284965 (x y : ℕ) :
    ¬(∃ n m, n ^ 2 = x ^ 2 + y + 1 ∧ m ^ 2 = y ^ 2 + 4 * x + 3) := by
  rintro ⟨n, m, h1, h2⟩
  have h3 : n > x := by
    by_contra h
    push_neg at h
    have h4 : n ≤ x := by omega
    have h5 : n ^ 2 ≤ x ^ 2 := by nlinarith
    nlinarith
  have h4 : m > y := by
    by_contra h
    push_neg at h
    have h5 : m ≤ y := by omega
    have h6 : m ^ 2 ≤ y ^ 2 := by nlinarith
    nlinarith
  have h5 : n = x + 1 := by
    have h6 : n > x := h3
    have h7 : n ≤ x + 1 := by
      nlinarith [sq_nonneg (n - (x + 1)), sq_nonneg (x + 1 - n), h1]
    have h8 : n = x + 1 := by
      omega
    exact h8
  have h8 : n = x + 1 := h5
  rw [h8] at h1
  have h9 : y = 2 * x := by
    nlinarith [h1]
  have h10 : m ^ 2 = 4 * x ^ 2 + 4 * x + 3 := by
    rw [show y = 2 * x by linarith [h9] ] at h2
    nlinarith [h2]
  have h11 : m ^ 2 = 4 * x ^ 2 + 4 * x + 3 := h10
  have h12 : m > 2 * x + 1 := by
    by_contra h
    push_neg at h
    have h13 : m ≤ 2 * x + 1 := by omega
    have h14 : m ^ 2 ≤ (2 * x + 1) ^ 2 := by nlinarith [h13]
    nlinarith [h11, h14, h13]
  have h13 : m < 2 * x + 2 := by
    by_contra h
    push_neg at h
    have h14 : m ≥ 2 * x + 2 := by omega
    have h15 : m ^ 2 ≥ (2 * x + 2) ^ 2 := by nlinarith [h14
    ]
    nlinarith [h11, h14, h15
    ]
  have h14 : m < 2 * x + 2 := h13
  have h15 : m > 2 * x + 1 := h12
  have h16 : m < 2 * x + 2 := h13
  omega