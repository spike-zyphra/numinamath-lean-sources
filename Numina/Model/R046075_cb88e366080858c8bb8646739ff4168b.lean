import Mathlib


theorem algebra_174218 (a : ℕ → ℚ) (ha0 : a 0 = 6) (ha1 : a 1 = 15)
    (han : ∀ n, a (n + 2) = 2 * (a (n + 1)) / (a n)) :
    a 99 = 2 / 3 := by

  have h8 : ∀ (n : ℕ), a n ≠ 0 := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      rw [ha0]
      norm_num
    | succ n =>
      cases n with
      | zero =>
        rw [ha1]
        norm_num
      | succ n =>
        have h9 : a (n + 2) = 2 * (a (n + 1)) / (a n) := han n
        have h10 : a (n) ≠ 0 := ih n (by linarith)
        have h11 : a (n + 1) ≠ 0 := ih (n + 1) (by linarith)
        have eq10 : a (n + 2) = 2 * (a (n + 1)) / (a n) := h9
        rw [eq10]
        field_simp [h10, h11]

  have h1 : ∀ n, a (n + 6) = a n := by
    intro n
    have eq1 : a (n + 2) = 2 * (a (n + 1)) / (a n) := han n
    have eq2 : a (n + 3) = 2 * (a (n + 2)) / (a (n + 1)) := by
      specialize han (n + 1)
      simpa using han
    have eq3 : a (n + 4) = 2 * (a (n + 3)) / (a (n + 2)) := by
      specialize han (n + 2)
      simpa using han
    have eq4 : a (n + 5) = 2 * (a (n + 4)) / (a (n + 3)) := by
      specialize han (n + 3)
      simpa using han
    have eq5 : a (n + 6) = 2 * (a (n + 5)) / (a (n + 4)) := by
      specialize han (n + 4)
      simpa using han

    have h10 : a n ≠ 0 := h8 n
    have h11 : a (n + 1) ≠ 0 := h8 (n + 1)
    have h12 : a (n + 2) ≠ 0 := h8 (n + 2)
    have h13 : a (n + 3) ≠ 0 := h8 (n + 3)
    have h14 : a (n + 4) ≠ 0 := h8 (n + 4)
    have h15 : a (n + 5) ≠ 0 := h8 (n + 5)

    rw [eq5, eq4, eq3, eq2, eq1]
    field_simp [h10, h11, h12, h13, h14, h15]
    all_goals ring

  have h100 : a 99 = a 3 := by
    have h93 : ∀ (k : ℕ), a (6 * k + 3) = a 3 := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        have h2 : a (6 * (k + 1) + 3) = a (6 * k + 3) := by
          have h4 : 6 * (k + 1) + 3 = (6 * k + 3) + 6 := by omega
          rw [h4]
          have h5 : a ((6 * k + 3) + 6) = a (6 * k + 3) := by
            specialize h1 (6 * k + 3)
            simpa using h1
          linarith
        have h3' : a (6 * (k + 1) + 3) = a (6 * k + 3) := h2
        rw [h3']
        linarith [ih]
    specialize h93 16
    norm_num at h93 ⊢
    all_goals linarith [h93]

  have ha3 : a 3 = 2 / 3 := by
    have eq1 : a 2 = 5 := by
      rw [han 0, ha1, ha0]
      norm_num
    rw [han 1, eq1, ha1]
    norm_num

  linarith [h100, ha3]