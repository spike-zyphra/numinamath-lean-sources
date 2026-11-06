import Mathlib

theorem algebra_130286 {a : ℕ → ℚ} (ha1 : a 1 = 1)
  (ha2 : a 2 = 1) (ha3 : a 3 = 2)
  (han : ∀ n ≥ 1, 3 * a (n + 3) = 4 * a (n + 2) + a (n + 1) - 2 * a n) :
  ∀ n ≥ 1, a n = ((1 : ℚ) + 15 * n - 27 / 2 * (-2 / 3) ^ n) / 25 := by
  intro n hn
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero =>
    exfalso 
    linarith
  | succ n =>
    cases n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n =>
      cases n with
      | zero =>
        rw [ha2]
        norm_num
      | succ n =>
        cases n with
        | zero =>
          rw [ha3]
          norm_num
        | succ n =>
          have eq1 := ih (n + 1) (by linarith)
          have eq2 := ih (n + 2) (by linarith)
          have eq3 := ih (n + 3) (by linarith)
          have h1 : 3 * a (n + 4) = 4 * a (n + 3) + a (n + 2) - 2 * a (n + 1) := by 
            specialize han (n + 1) (by linarith)
            simpa using han
          have eq1' : n + 1 ≥ 1 := by linarith
          have eq2' : n + 2 ≥ 1 := by linarith
          have eq3' : n + 3 ≥ 1 := by linarith
          have eq4 : a (n + 4) = ((1 : ℚ) + 15 * (↑n + 4) - 27 / 2 * (-2 / 3) ^ (n + 4)) / 25 := by
            have eq6 : 3 * a (n + 4) = 4 * ((1 : ℚ) + 15 * (↑n + 3) - 27 / 2 * (-2 / 3) ^ (n + 3)) / 25 + ((1 : ℚ) + 15 * (↑n + 2) - 27 / 2 * (-2 / 3) ^ (n + 2)) / 25 - 2 * ((1 : ℚ) + 15 * (↑n + 1) - 27 / 2 * (-2 / 3) ^ (n + 1)) / 25 := by 
              rw [show a (n + 1) = ((1 : ℚ) + 15 * (↑n + 1) - 27 / 2 * (-2 / 3) ^ (n + 1)) / 25 by 
                  have eq1a := eq1 (by linarith)
                  simpa using eq1a 
                ] at h1
              rw [show a (n + 2) = ((1 : ℚ) + 15 * (↑n + 2) - 27 / 2 * (-2 / 3) ^ (n + 2)) / 25 by 
                  have eq2a := eq2 (by linarith)
                  simpa using eq2a 
                ] at h1
              rw [show a (n + 3) = ((1 : ℚ) + 15 * (↑n + 3) - 27 / 2 * (-2 / 3) ^ (n + 3)) / 25 by 
                  have eq3a := eq3 (by linarith)
                  simpa using eq3a 
                ] at h1
              linarith
            have eq7 : a (n + 4) = (4 * ((1 : ℚ) + 15 * (↑n + 3) - 27 / 2 * (-2 / 3) ^ (n + 3)) / 25 + ((1 : ℚ) + 15 * (↑n + 2) - 27 / 2 * (-2 / 3) ^ (n + 2)) / 25 - 2 * ((1 : ℚ) + 15 * (↑n + 1) - 27 / 2 * (-2 / 3) ^ (n + 1)) / 25) / 3 := by 
              linarith 
            rw [eq7]
            field_simp 
            <;> ring_nf
          simp [eq4]
          <;> ring_nf