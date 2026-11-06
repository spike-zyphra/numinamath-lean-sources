import Mathlib

/- Find the units digit of $16^{17} \times 17^{18} \times 18^{19}$. -/
theorem number_theory_23216 : (16^17 * 17^18 * 18^19) % 10 = 8 := by
  -- $16 \equiv 6 \pmod{10}$
  have h1 : 16 ≡ 6 [MOD 10] := by
    exact rfl
  -- $16^{17} \equiv 6^{17} \pmod{10}$
  have h1' : 16^17 ≡ 6^17 [MOD 10] := by
    apply Nat.ModEq.pow 17 h1
  -- $17 \equiv 7 \pmod{10}$
  have h2 : 17 ≡ 7 [MOD 10] := by
    exact rfl
  -- $17^{18} \equiv 7^{18} \pmod{10}$
  have h2' : 17^18 ≡ 7^18 [MOD 10] := by
    apply Nat.ModEq.pow 18 h2
  -- $18 \equiv 8 \pmod{10}$
  have h3 : 18 ≡ 8 [MOD 10] := by
    exact rfl
  -- $18^{19} \equiv 8^{19} \pmod{10}$
  have h3' : 18^19 ≡ 8^19 [MOD 10] := by
    apply Nat.ModEq.pow 19 h3
  -- $16^{17} \times 17^{18} \times 18^{19} \equiv 6^{17} \times 7^{18} \times 8^{19} \pmod{10}$
  have h4 : 16^17 * 17^18 * 18^19 ≡ 6^17 * 7^18 * 8^19 [MOD 10] := by
    apply Nat.ModEq.mul h1' (Nat.ModEq.mul h2' h3')
  -- $6^{17} \times 7^{18} \times 8^{19} = (6 \times 7 \times 8)^{17} \times 7 \times 8^2$
  have h5 : 6^17 * 7^18 * 8^19 = (6 * 7 * 8)^17 * (7 * 8^2) := by
    ring
  rw [h5] at h4
  -- $6 \times 7 \times 8 \equiv 8 \pmod{10}$
  have h8 : 6 * 7 * 8^2 ≡ 8 [MOD 10] := by
    exact rfl
  apply Nat.ModEq.trans h4 at h8
  exact h8