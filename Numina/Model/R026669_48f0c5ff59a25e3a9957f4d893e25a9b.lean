import Mathlib

theorem number_theory_40806 (a b c : ℝ) (n : ℕ) (h : 0 < n) (h' : a ^ n + b ^ n = c ^ n ∧ a ^ (n + 1) + b ^ (n + 1) = c ^ (n + 1) ∧ a ^ (n + 2) + b ^ (n + 2) = c ^ (n + 2)) : a * b * c = 0 := by
  rcases h' with ⟨h1, h2, h3⟩
  have eq1 : a ^ n * (a - c) + b ^ n * (b - c) = 0 := by
    have eq2 : a ^ (n + 1) + b ^ (n + 1) = c ^ (n + 1) := h2
    have eq3 : c ^ (n + 1) = c * (c ^ n) := by ring
    rw [eq3] at eq2
    have eq4 : a ^ (n + 1) = a * (a ^ n) := by ring
    have eq5 : b ^ (n + 1) = b * (b ^ n) := by ring
    rw [eq4, eq5] at eq2
    have h1' : c ^ n = a ^ n + b ^ n := by linarith [h1]
    rw [h1'] at eq2
    nlinarith
  have eq2 : a ^ n * (a - c) * (a + c) + b ^ n * (b - c) * (b + c) = 0 := by
    have eq3 : a ^ (n + 2) + b ^ (n + 2) = c ^ (n + 2) := h3
    have eq4 : a ^ (n + 2) = a ^ 2 * (a ^ n) := by ring
    have eq5 : b ^ (n + 2) = b ^ 2 * (b ^ n) := by ring
    have eq6 : c ^ (n + 2) = c ^ 2 * (c ^ n) := by ring
    rw [eq4, eq5, eq6] at eq3
    have h1' : c ^ n = a ^ n + b ^ n := by linarith [h1]
    rw [h1'] at eq3
    nlinarith
  have eq3 : b ^ n * (b - c) * (b - a) = 0 := by
    have eq4 : a ^ n * (a - c) * (a + c) + b ^ n * (b - c) * (b + c) = 0 := eq2
    have eq5 : a ^ n * (a - c) = -b ^ n * (b - c) := by linarith [eq1]
    rw [eq5] at eq4
    nlinarith
  cases' (mul_eq_zero.mp eq3) with eq4 eq5
  · cases' (mul_eq_zero.mp eq4) with eq6 eq7
    · -- case $b^n = 0$
      have eq8 : b ^ n = 0 := eq6
      have eq9 : b = 0 := by
        have h10 : b ^ n = 0 := eq8
        have h11 : b = 0 := by
          have h12 : n > 0 := by linarith
          have h13 : b ^ n = 0 := h10
          have h14 : b = 0 := by
            apply pow_eq_zero 
            exact h13
          exact h14
        assumption
      rw [eq9]
      simp
    · -- case $b - c = 0$
      have eq10 : b = c := by linarith
      have eq11 : a ^ n = 0 := by
        have h12 : a ^ n + b ^ n = c ^ n := h1
        rw [show c = b by linarith [eq10]] at h12
        nlinarith
      have eq12 : a = 0 := by
        have h13 : a ^ n = 0 := eq11
        have h14 : a = 0 := by
          have h15 : n > 0 := by linarith
          have h16 : a ^ n = 0 := h13
          have h17 : a = 0 := by
            apply pow_eq_zero 
            exact h16
          exact h17
        assumption
      rw [eq12]
      simp
  · -- case $b - a = 0$
    have eq18 : b = a := by linarith
    have eq19 : 2 * (a ^ n) = c ^ n := by
      have h12 : a ^ n + b ^ n = c ^ n := h1
      rw [show b = a by linarith [eq18]] at h12
      linarith
    have eq20 : 2 * (a ^ (n + 1)) = c ^ (n + 1) := by
      have h12 : a ^ (n + 1) + b ^ (n + 1) = c ^ (n + 1) := h2
      rw [show b = a by linarith [eq18]] at h12
      linarith
    have eq21 : a ^ n * (a - c) = 0 := by
      have h22 : 2 * (a ^ (n + 1)) = c ^ (n + 1) := eq20
      have h23 : 2 * (a ^ (n + 1)) = 2 * (a) * (a ^ n) := by ring
      rw [h23] at h22
      have h24 : c ^ (n + 1) = c * (c ^ n) := by ring
      rw [h24] at h22
      have h25 : c ^ n = 2 * (a ^ n) := by linarith [eq19]
      rw [h25] at h22
      nlinarith
    cases' (mul_eq_zero.mp eq21) with eq22 eq23
    · -- case $a^n = 0$
      have eq24 : a = 0 := by
        have h13 : a ^ n = 0 := eq22
        have h14 : a = 0 := by
          have h15 : n > 0 := by linarith
          have h16 : a ^ n = 0 := h13
          have h17 : a = 0 := by
            apply pow_eq_zero 
            exact h16
          exact h17
        assumption
      rw [eq24]
      simp
    · -- case $a - c = 0$
      have eq25 : a = c := by linarith
      have eq26 : a ^ n = 0 := by
        have h12 : 2 * (a ^ n) = c ^ n := eq19
        rw [show c = a by linarith [eq25]] at h12
        nlinarith
      have eq27 : a = 0 := by
        have h13 : a ^ n = 0 := eq26
        have h14 : a = 0 := by
          have h15 : n > 0 := by linarith
          have h16 : a ^ n = 0 := h13
          have h17 : a = 0 := by
            apply pow_eq_zero 
            exact h16
          exact h17
        assumption
      rw [eq27]
      simp