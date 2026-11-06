import Mathlib

/- Let $d$ be a positive integer not equal to $2, 5, 13$. Prove that in the set $\{2, 5, 13, d\}$, there exist two distinct elements $a, b$ such that $ab-1$ is not a perfect square. -/
theorem number_theory_176725 (d : ℕ) (hd : d > 0) (h2 : d ≠ 2) (h5 : d ≠ 5) (h13 : d ≠ 13) :
    ∃ a b, ((a = 2 ∧ b = 5) ∨ (a = 2 ∧ b = 13) ∨ (a = 5 ∧ b = 13) ∨ (a = 2 ∧ b = d) ∨
    (a = 5 ∧ b = d) ∨ (a = 13 ∧ b = d)) ∧ ¬ ∃ m, m^2 = a * b - 1 := by
  -- prove by contradiction
  by_contra h
  push_neg at h
  -- then 2, d; 5, d; 13, d all will give squares
  have h2d := h 2 d
  simp at h2d
  have h5d := h 5 d
  simp at h5d
  have h13d := h 13 d
  simp at h13d
  clear h
  obtain ⟨x, hx⟩ := h2d
  obtain ⟨y, hy⟩ := h5d
  obtain ⟨z, hz⟩ := h13d
  -- from equatin x is odd
  have h_odd_x : Odd x := by
    apply Nat.Odd.of_mul_right (m := x)
    rw [← sq, hx]
    apply Nat.Even.sub_odd
    . omega
    . simp
    . decide
  -- write x as 2 * n + 1
  obtain ⟨n, hxn⟩ := h_odd_x
  rw [hxn] at hx
  ring_nf at hx
  -- then d is odd
  replace hx : d = 2 * (n^2 + n) + 1 := by omega
  have h_odd_d : Odd d := by
    rw [hx]
    simp
  -- then by hy and hz, we have y and z even
  have h_even_y : Even y := by
    rw [← Nat.even_pow' (show 2 ≠ 0 by norm_num), hy]
    apply Nat.Odd.sub_odd
    . apply Odd.mul (by decide) h_odd_d
    . decide
  have h_even_z : Even z := by
    rw [← Nat.even_pow' (show 2 ≠ 0 by norm_num), hz]
    apply Nat.Odd.sub_odd
    . apply Odd.mul (by decide) h_odd_d
    . decide
  -- write y and z as 2 * p, 2 * q
  obtain ⟨p, hp⟩ := h_even_y
  obtain ⟨q, hq⟩ := h_even_z
  rw [hp] at hy
  rw [hq] at hz
  ring_nf at hy hz
  rw [show d * 13 = d * 5 + d * 8 by ring] at hz
  rw [show d * 5 = p^2 * 4 + 1 by omega] at hz
  -- then q^2 = p^2 + d
  replace hz : q^2 = p^2 + d * 2 := by omega
  -- by caseworking on p being even or odd, we find q has same parity and then d is even
  have h_even_d : Even d := by
    obtain h_even_p | h_odd_p := Nat.even_or_odd p
    . have h_even_q : Even q := by
        rw [← Nat.even_pow' (show 2 ≠ 0 by norm_num), hz]
        apply Even.add
        . rwa [Nat.even_pow' (show 2 ≠ 0 by norm_num)]
        . rw [mul_comm]
          simp
      obtain ⟨a, ha⟩ := h_even_p
      obtain ⟨b, hb⟩ := h_even_q
      rw [ha, hb] at hz
      ring_nf at hz
      replace hz : d = 2 * (b^2 - a^2) := by omega
      rw [hz]
      simp
    . have h_odd_q : Odd q := by
        apply Nat.Odd.of_mul_right (m := q)
        rw [← sq, hz]
        apply Odd.add_even
        . rw [sq]
          apply Odd.mul <;> assumption
        . rw [mul_comm]
          simp
      obtain ⟨a, ha⟩ := h_odd_p
      obtain ⟨b, hb⟩ := h_odd_q
      rw [ha, hb] at hz
      ring_nf at hz
      replace hz : d = 2 * ((b^2 + b) - (a^2 + a)) := by omega
      rw [hz]
      simp
  -- this is contradiction
  rw [← Nat.not_odd_iff_even] at h_even_d
  contradiction