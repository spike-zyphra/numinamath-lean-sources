import Mathlib

/- Let $a$ be an integer. Determine the remainder when $a^{82}$ is divided by 11. Show that the answer is $(a \pmod{11})^2 \pmod{11}$. -/
theorem number_theory_635167 (a : ℤ) :
    a ^ 82 % 11 = (a % 11) ^ 2 % 11 := by
  -- We first show that 11 is a prime number.
  have inst : Fact (11 : ℕ).Prime := ⟨by norm_num⟩
  -- It suffices to show that a ^ 82 = a ^ 2 as a member of ℤ / 11ℤ.
  suffices (a ^ 82 : ZMod 11) = a ^ 2 by
    -- We rewrite the goal.
    change a ^ 82 ≡ (a % 11) ^ 2 [ZMOD (11 : ℕ)]
    -- We apply the lemma `ZMod.intCast_eq_intCast_iff`.
    rw [← ZMod.intCast_eq_intCast_iff]
    simp
    change (a ^ 82 : ZMod 11) = ↑(a % (11 : ℕ)) ^ 2
    -- We use the lemma `ZMod.intCast_mod`.
    rwa [ZMod.intCast_mod]
  -- We show that a ^ 82 = a ^ 2 as a member of ℤ / 11ℤ.
  calc (a ^ 82 : ZMod 11)
    -- a ^ 82 = a ^ (11 * 7 + 5)
    _ = a ^ (11 * 7 + 5) := by norm_num
    -- ... = (a ^ 11) ^ 7 * a ^ 5
    _ = (a ^ 11) ^ 7 * a ^ 5 := by rw [pow_add, ← pow_mul]
    -- a ^ 11 = a by Fermat's little theorem
    _ = a ^ (7 + 5) := by rw [ZMod.pow_card, ← pow_add]
    -- So a ^ 82 = a ^ 12 = a ^ 11 * a
    _ = a ^ 11 * a := by rw [pow_succ]
    -- a ^ 11 = a by Fermat's little theorem
    _ = a ^ 2 := by rw [ZMod.pow_card, sq]