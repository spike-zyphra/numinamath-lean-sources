import Mathlib

theorem number_theory_215340 (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    a % 2 = b % 2 ↔ ∃ c d : ℤ, 0 < c ∧ 0 < d ∧ a^2 + b^2 + c^2 + 1 = d^2 := by
  constructor
  · -- Assume a % 2 = b % 2 (same parity)
    intro h
    have h1 : (a % 2 : ℤ) = (b % 2 : ℤ) := h
    have h2 : (a + b) % 2 = 0 := by
      omega
    -- Show $a^2 + b^2$ is even.
    have h3 : (a ^ 2 + b ^ 2) % 2 = 0 := by
      have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases ha2 with (h | h)
      · -- a % 2 = 0
        rcases hb2 with (h2 | h2)
        · -- b % 2 = 0
          simp [pow_two, Int.add_emod, Int.mul_emod, h, h2]
        · -- b % 2 = 1
          omega
      · -- a % 2 = 1
        rcases hb2 with (h2 | h2)
        · -- b % 2 = 0
          omega
        · -- b % 2 = 1
          simp [pow_two, Int.add_emod, Int.mul_emod, h, h2]
    -- Show the existence of c and d such that a^2 + b^2 + c^2 + 1 = d^2 
    have h4 : ∃ c d : ℤ, 0 < c ∧ 0 < d ∧ a^2 + b^2 + c^2 + 1 = d^2 := by
      have h5 : (a ^ 2 + b ^ 2) % 2 = 0 := h3
      have h6 : ∃ k : ℤ, a ^ 2 + b ^ 2 = 2 * k := by
        have : (a ^ 2 + b ^ 2) % 2 = 0 := h5
        refine' ⟨(a ^ 2 + b ^ 2) / 2, by omega⟩
      rcases h6 with ⟨k, hk⟩
      use k
      use k + 1
      have hk_pos : 0 < k := by
        nlinarith [show 0 < a by linarith, show 0 < b by linarith]
      constructor
      · -- 0 < c
        linarith [hk_pos]
      constructor
      · -- 0 < d
        linarith [hk_pos]
      · -- a^2 + b^2 + c^2 + 1 = d^2
        nlinarith [show a^2 + b^2 = 2 * k by linarith [hk]]
    exact h4
  · -- Assume the existence, prove $a \equiv b \mod 2$.
    intro h
    rcases h with ⟨c, d, hc, hd, heq⟩
    have h1_mod4 : (a ^ 2 : ℤ) % 4 = 0 ∨ (a ^ 2 : ℤ) % 4 = 1 := by
      have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
      rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    have h2_mod4 : (b ^ 2 : ℤ) % 4 = 0 ∨ (b ^ 2 : ℤ) % 4 = 1 := by
      have h1 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
      rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    have h3_mod4 : (c ^ 2 : ℤ) % 4 = 0 ∨ (c ^ 2 : ℤ) % 4 = 1 := by
      have h1 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega
      rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    have h4_mod4 : (d ^ 2 : ℤ) % 4 = 0 ∨ (d ^ 2 : ℤ) % 4 = 1 := by
      have h1 : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
      rcases h1 with (h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    have h5 : (a ^ 2 + b ^ 2 + c ^ 2 + 1) % 4 = (d ^ 2) % 4 := by
      omega
    have h6 : a % 2 = b % 2 := by
      by_contra h
      push_neg at h
      have h7 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have h8 : b % 2 = 0 ∨ b % 2 = 1 := by omega
      have h9 : a % 2 ≠ b % 2 := by
        omega
      rcases h7 with (h7 | h7)
      · -- a % 2 = 0
        rcases h8 with (h8 | h8)
        · -- b % 2 = 0
          exfalso
          omega
        · -- b % 2 = 1
          have ha2 : (a ^ 2 : ℤ) % 4 = 0 := by
            have h1 : a % 2 = 0 := h7
            have : a % 4 = 0 ∨ a % 4 = 2 := by omega
            rcases this with (h2 | h2)
            all_goals simp [pow_two, Int.add_emod, Int.mul_emod, h2]
          have hb2 : (b ^ 2 : ℤ) % 4 = 1 := by
            have h1 : b % 2 = 1 := h8
            have : b % 4 = 1 ∨ b % 4 = 3 := by omega
            rcases this with (h2 | h2)
            all_goals simp [pow_two, Int.add_emod, Int.mul_emod, h2]
          omega
      · -- a % 2 = 1
        rcases h8 with (h8 | h8)
        · -- b % 2 = 0
          have ha2 : (a ^ 2 : ℤ) % 4 = 1 := by
            have h1 : a % 2 = 1 := h7
            have : a % 4 = 1 ∨ a % 4 = 3 := by omega
            rcases this with (h2 | h2)
            all_goals simp [pow_two, Int.add_emod, Int.mul_emod, h2]
          have hb2 : (b ^ 2 : ℤ) % 4 = 0 := by
            have h1 : b % 2 = 0 := h8
            have : b % 4 = 0 ∨ b % 4 = 2 := by omega
            rcases this with (h2 | h2)
            all_goals simp [pow_two, Int.add_emod, Int.mul_emod, h2]
          omega
        · -- b % 2 = 1
          exfalso
          omega
    exact h6