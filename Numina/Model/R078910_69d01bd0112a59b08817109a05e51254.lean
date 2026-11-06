import Mathlib

theorem algebra_324454 (a b c : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 2 + b * x + c)
    (h0 : |f 0| ≤ 1) (h1 : |f 1| ≤ 1) (h2 : |f (-1)| ≤ 1) :
    |f 2| ≤ 7 := by
  have h_eq1 : f 0 = c := by
    rw [hf]
    ring
  have h_eq2 : f 1 = a + b + c := by
    rw [hf]
    ring
  have h_eq3 : f (-1) = a - b + c := by
    rw [hf]
    ring
  have h_eq4 : f 2 = 4 * a + 2 * b + c := by
    rw [hf]
    ring
  have h0' : |c| ≤ 1 := by
    have : f 0 = c := h_eq1
    rw [this] at h0
    exact h0
  have h1' : |a + b + c| ≤ 1 := by
    have : f 1 = a + b + c := h_eq2
    rw [this] at h1
    exact h1
  have h2' : |a - b + c| ≤ 1 := by
    have : f (-1) = a - b + c := h_eq3
    rw [this] at h2
    exact h2
  have h3 : -1 ≤ c ∧ c ≤ 1 := by
    constructor
    · linarith [abs_le.mp h0']
    · linarith [abs_le.mp h0']
  have h4 : -1 ≤ a + b + c ∧ a + b + c ≤ 1 := by
    constructor
    · linarith [abs_le.mp h1']
    · linarith [abs_le.mp h1']
  have h5 : -1 ≤ a - b + c ∧ a - b + c ≤ 1 := by
    constructor
    · linarith [abs_le.mp h2']
    · linarith [abs_le.mp h2']
  have h7 : -7 ≤ (4 * a + 2 * b + c : ℝ) := by
    linarith [abs_le.mp h0', abs_le.mp h1', abs_le.mp h2']
  have h8 : (4 * a + 2 * b + c : ℝ) ≤ 7 := by
    linarith [abs_le.mp h0', abs_le.mp h1', abs_le.mp h2']
  have h9 : -7 ≤ f 2 := by 
    have h10 : f 2 = 4 * a + 2 * b + c := h_eq4
    linarith [h10, h7]
  have h10 : f 2 ≤ 7 := by 
    have h11 : f 2 = 4 * a + 2 * b + c := h_eq4
    linarith [h11, h8]
  apply abs_le.mpr
  constructor <;> linarith