import Mathlib

theorem algebra_190645 (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
    (h1 : ∀ x, f x + f (x + a) = 1) (h2 : ∃ c, ∀ x, c < x ∧ x < c + a → f x < 1/2) :
    IsLeast {T | 0 < T ∧ ∀ x, f (x + T) = f x} (2 * a) := by 
  have period_2a : ∀ x, f (x + 2 * a) = f x := by
    intro x
    rw [two_mul, ←add_assoc]
    linarith [h1 x, h1 (x + a)]

  constructor
  · -- Show 2*a is in the set, so prove $2 a > 0$ and that $f$ is periodic with period $2 a$.
    constructor
    · -- $2a$ is positive
      nlinarith
    · -- Show f is periodic with period 2*a.
      exact period_2a

  · -- Show that 2*a is the minimum element in the set
    intro T ⟨hT_pos, hT_period⟩
    by_contra h
    push_neg at h
    rcases h2 with ⟨c, hc⟩

    have h4 := hc (c + (T / 2)) ⟨by nlinarith, by nlinarith⟩

    have h5 : f (c + T / 2) = f (c - T / 2) := by
      have h6 := hT_period (c - T / 2)
      have eq1 : (c - T / 2) + T = c + T / 2 := by ring_nf
      rw [eq1] at h6
      linarith [h6]

    have h6 := h1 (c - T / 2)
    have h7 : c < (c + a - T / 2) := by
      nlinarith [hT_pos, h]

    have h8 : (c + a - T / 2) < c + a := by 
      nlinarith [hT_pos, h]

    have h9 := hc (c + a - T / 2) ⟨h7, h8⟩

    have h10 : f (c + a - T / 2) > 1 / 2 := by
      have eq1 : f (c - T / 2) < 1 / 2 := by
        nlinarith [h5, h4]
      have eq2 : f (c - T / 2 + a) = 1 - f (c - T / 2) := by
        have h6' := h1 (c - T / 2)
        linarith
      have eq3 : f (c + a - T / 2) = f (c - T / 2 + a) := by
        ring_nf
      nlinarith [eq2, eq1, eq3]

    linarith [h9, h10]