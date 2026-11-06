import Mathlib

/- Let's prove that the parity of positive integers $a, b$ is the same if and only if there exist positive integers $c, d$ such that $a^{2}+b^{2}+c^{2}+1=d^{2}$. -/
theorem number_theory_215340 (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    a % 2 = b % 2 ↔ ∃ c d : ℤ, 0 < c ∧ 0 < d ∧ a^2 + b^2 + c^2 + 1 = d^2 := by
  constructor
  . rintro h
    -- if a, b have same parity, then 2 ∣ a^2 + b^2
    have : 2 ∣ a^2 + b^2 := by
      rw [Int.dvd_iff_emod_eq_zero, Int.add_emod, sq, sq, Int.mul_emod a a, Int.mul_emod b b, h]
      ring_nf
      rw [Int.mul_emod_left]
    -- also 2 ≤ a^2 + b^2
    have : 2 ≤ a^2 + b^2 := by
      rw [show (2 : ℤ) = 1 + 1 by norm_num]
      apply add_le_add
      . exact one_le_sq_iff₀ (ha.le) |>.mpr (by omega)
      . exact one_le_sq_iff₀ (hb.le) |>.mpr (by omega)
    -- now we'll use (a^2 + b^2)/2, (a^2 + b^2)/2 + 1 as c, d
    use (a^2 + b^2)/2, (a^2 + b^2)/2 + 1
    -- the two facts help us prove that equation is satisfied
    and_intros
    . omega
    . omega
    . ring_nf
      rw [Int.ediv_mul_cancel (by assumption)]
      ring
  -- the equation is true then, we convert the goal in terms of ZMod 4
  . rintro ⟨c, d, hc, hd, h⟩
    rw [← Int.emod_emod_of_dvd (k := 4), ← Int.emod_emod_of_dvd (k := 4) b]
    pick_goal 2; norm_num
    pick_goal 2; norm_num
    rw [show (4 : ℤ) = ↑(4 : ℕ) by norm_cast, ← ZMod.coe_intCast, ← ZMod.coe_intCast]
    -- prove that in ZMod 4, x^2 = 0 or 1
    have aux (x : ZMod 4) : x^2 = 0 ∨ x^2 = 1 := by
      fin_cases x
      all_goals simp
      all_goals norm_cast
    -- next prove that target x % 2 = x^2 % 2 for ZMod 4
    have aux2 (x : ZMod 4) : (x^2).cast % (2 : ℤ) = x.cast % (2 : ℤ) := by
      fin_cases x
      all_goals simp
      all_goals norm_cast
    -- now for any 4 variables from ZMod 4, the equation applies, parity same, this is by brute force on square values
    have (a b c d : ZMod 4) (h : a^2 + b^2 + c^2 + 1 = d^2) : a.cast % (2 : ℤ) = b.cast % (2 : ℤ) := by
      rw [← aux2, ← aux2 b]
      obtain hx | hx := aux a
      all_goals (
        rw [hx] at h ⊢
        obtain hx | hx := aux b
        all_goals (
          rw [hx] at h ⊢
        )
        obtain hx | hx := aux c
        all_goals (
          rw [hx] at h
          obtain hx | hx := aux d
          all_goals (
            rw [hx] at h
            norm_cast at h
          )
        )
      )
    -- we'll apply the fact to prove goal, so we just need to convert equation in terms of ZMod 4
    apply this a b c d
    norm_cast
    rw [h]