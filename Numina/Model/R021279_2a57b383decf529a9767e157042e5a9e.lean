import Mathlib


theorem algebra_240110 {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h1 : b * 32 = a * 2 * (b - 5)) (h2 : b * 32 = a * b - 320) :
    b = 20 := by
  have h3 : b ≥ 5 := by
    by_contra h
    push_neg at h
    have h4 : b < 5 := by omega
    interval_cases b <;> omega

  have eq4 : a * b = 320 + 32 * b := by
    omega

  have eq6 : a * (b - 5) = 16 * b := by
    have eq14 : b * 16 = a * (b - 5) := by
      have eq12 : b * 32 = a * 2 * (b - 5) := h1
      have eq15 : b * 16 * 2 = a * 2 * (b - 5) := by
        nlinarith
      have eq16 : b * 16 = a * (b - 5) := by
        nlinarith [eq15]
      exact eq16
    have eq17 : a * (b - 5) = 16 * b := by
      have eq18 : b * 16 = a * (b - 5) := eq14
      nlinarith [eq18]
    exact eq17

  have eq7 : 5 * a = 320 + 16 * b := by
    have eq8 : a * (b - 5) = 16 * b := eq6
    have eq4' : a * b = 320 + 32 * b := eq4
    have eq9 : b ≥ 5 := h3
    have eq10 : 5 * a = 320 + 16 * b := by
      have eq11 : a * (b - 5) = 16 * b := eq8
      have eq12 : a * b = 320 + 32 * b := eq4
      have eq13 : 5 * a = 320 + 16 * b := by
        have eq14 : a * (b - 5) = 16 * b := eq11
        have eq15 : a * b = 320 + 32 * b := eq12
        have eq16 : 5 * a = 320 + 16 * b := by
          have eq17 : a * b = 320 + 32 * b := eq15
          have eq18 : a * (b - 5) = 16 * b := eq14
          cases b with
          | zero => omega
          | succ b =>
            cases b with
            | zero => omega
            | succ b =>
              cases b with
              | zero => omega
              | succ b =>
                cases b with
                | zero => omega
                | succ b =>
                  simp [Nat.mul_sub_left_distrib, Nat.mul_add, Nat.mul_assoc] at eq18 eq17 ⊢
                  all_goals
                    omega
        exact eq16
      exact eq13
    exact eq10


  have eq10 : ∃ k : ℕ, b = 5 * k := by
    have h9 : b % 5 = 0 := by
      omega
    have : ∃ k, b = 5 * k := by
      refine' ⟨b / 5, by omega⟩
    exact this

  rcases eq10 with ⟨k, hk⟩

  have eq11 : 5 * a = 320 + 16 * (5 * k) := by
    rw [show b = 5 * k by linarith [hk]] at eq7
    linarith

  have eq12 : a = 64 + 16 * k := by
    omega

  have eq13 : (64 + 16 * k) * (5 * k) = 320 + 32 * (5 * k) := by
    rw [show a = 64 + 16 * k by linarith [eq12], show b = 5 * k by linarith [hk]] at eq4
    linarith [eq4]

  have eq14 : 80 * k ^ 2 + 160 * k = 320 := by
    nlinarith

  have eq15 : k ≤ 2 := by
    nlinarith

  interval_cases k <;> omega