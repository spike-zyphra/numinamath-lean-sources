import Mathlib

open Real
/--
Problem statement:
Find two lines of symmetry of the graph of the function $y=x+\frac{1}{x}$. Express your answer as two equations of the form $y=a x+b$.
Solution:
$y=(1+\sqrt{2}) x$ and $y=(1-\sqrt{2}) x$
-/

theorem algebra_608684
(k: ℝ)
(hk : k ≠ 0)
(f : ℝ → ℝ)
(hf : f = fun x => x + 1 / x)
(hsymm : ∀ x1, ∃ x2, x2 ≠ 0 ∧ x2 ≠ x1 ∧  x1 + x2 ≠ 0 ∧ (f x2 - f x1) / (x2 - x1) = -1 / k ∧ (f x1+f x2) / 2 = k * (x1 + x2) / 2):
k = 1-sqrt 2 ∨ k = 1+sqrt 2:= by

  have h1 := hsymm 1
  obtain ⟨x, ⟨hx_ne_zero, hx_ne_one, hx_add_ne_zero, hx⟩⟩ := h1
  have : x - 1 ≠ 0 := by
    by_contra h
    have : x = 1 := by linarith
    contradiction
  rw [hf] at hx
  field_simp at hx
  rw [← pow_two, one_add_one_eq_two] at hx
  have : (x ^ 2 + 1 - x * 2) = (x - 1) ^ 2 := by ring
  rw [this] at hx
  have : (2 * x + (x ^ 2 + 1)) = (x + 1) ^ 2 := by ring
  rw [this] at hx

  have h2 : (x - 1) * k = -x := by
    have := hx.1
    rw [pow_two, mul_assoc, (by ring : -(x * (x - 1)) = (x - 1) * (-x))] at this
    apply mul_left_cancel₀ at this
    exact this
    assumption

  have h3 : (x + 1) * 2 = k * (x * 2) := by
    have := hx.2
    rw [pow_two, mul_assoc, (by ring : k * (1 + x) * (x * 2) = (x + 1) * (k * (x * 2)))] at this
    apply mul_left_cancel₀ at this
    exact this
    have : x + 1 ≠ 0 := by rw [add_comm]; exact hx_add_ne_zero
    exact this

  have h4 : (x - 1) * (x + 1) * 2 = (x - 1) * k * (x * 2) := by
    rw [mul_assoc, h3]
    ring

  rw [h2] at h4

  have h5 : x ^ 2 = 1 / 2 := by linarith
  have h6 : x = -1 / sqrt 2 ∨ x = 1 / sqrt 2 := by
    have : 1/2 = (1 / sqrt 2)^2 := by
      rw [div_pow]
      simp

    rw [this] at h5
    apply eq_or_eq_neg_of_sq_eq_sq at h5
    cases' h5 with h51 h52
    . right; exact h51
    . left
      field_simp at h52
      rw[← h52]
      field_simp

  have h7 : k = 1 - sqrt 2 ∨ k = 1 + sqrt 2 := by
    cases' h6 with h6_left h6_right
    . left
      rw [h6_left] at h2
      field_simp at h2
      have : (-1 - sqrt 2) * (1 - sqrt 2)= 1 := by
        ring_nf
        simp
        ring
      nth_rw 2 [← this] at h2
      field_simp at h2
      cases' h2 with h21 h22
      . exact h21
      . have : 1 + sqrt 2 > 0 := by positivity
        linarith

    . right
      rw [h6_right] at h2
      field_simp at h2
      have : (1 - sqrt 2) * (1 + sqrt 2) = -1 := by
        ring_nf
        simp
        ring
      rw [← this] at h2
      field_simp at h2
      cases' h2 with h21 h22
      . exact h21
      . have : 1 - √2 ≠ 0 := by
          by_contra h
          have : 1 = sqrt 2 := by linarith
          have : 1^2 = (sqrt 2)^2 := by rw[this]
          simp at this
        tauto

  exact h7
