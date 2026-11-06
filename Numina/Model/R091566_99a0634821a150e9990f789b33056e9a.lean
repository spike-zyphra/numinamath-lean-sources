import Mathlib

theorem algebra_317527 (s : ℂ) (h₀ : s^7 = 1) (h₁ : s ≠ 1) :
    s * (s + 1) * (s^2 - s + 1) * (s^2 + s + 1) = -1 := by
  have h3 : s - 1 ≠ 0 := by
    intro h
    apply h₁
    exact eq_of_sub_eq_zero h
  have h4 : s^7 - 1 = 0 := by
    rw [h₀]
    ring
  have h5 : s^7 - 1 = (s - 1) * (s^6 + s^5 + s^4 + s^3 + s^2 + s + 1) := by
    ring_nf
    <;> simp [pow_two, pow_three, pow_succ]
    <;> ring_nf
    <;> simp [sub_eq_add_neg]
    <;> ring
  rw [h5] at h4
  have h2 : s^6 + s^5 + s^4 + s^3 + s^2 + s + 1 = 0 := by
    apply (mul_eq_zero.mp h4).resolve_left
    exact h3
  have eq1 : s * (s + 1) * (s^2 - s + 1) * (s^2 + s + 1) = s^6 + s^5 + s^4 + s^3 + s^2 + s := by
    ring_nf
  have eq2 : s^6 + s^5 + s^4 + s^3 + s^2 + s = -1 := by
    have h_eq : s^6 + s^5 + s^4 + s^3 + s^2 + s + 1 = 0 := h2
    have : s^6 + s^5 + s^4 + s^3 + s^2 + s = -1 := by
      calc
        s^6 + s^5 + s^4 + s^3 + s^2 + s = (s^6 + s^5 + s^4 + s^3 + s^2 + s + 1) - 1 := by ring
        _ = 0 - 1 := by rw [h_eq]
        _ = -1 := by ring
    exact this
  rw [eq1]
  exact eq2