import Mathlib

/-Find the least positive four-digit solution to the following system of congruences. \begin{align*}
7x &\equiv 21 \pmod{14} \\
2x+13 &\equiv 16 \pmod{9} \\
-2x+1 &\equiv x \pmod{25} \\
\end{align*}-/
theorem number_theory_12801:
    IsLeast {(x : ℤ) | 1000 ≤ x ∧ x < 10000 ∧ 7 * x ≡ 21 [ZMOD 14] ∧ 2 * x + 13 ≡ 16 [ZMOD 9] ∧ -2 * x + 1 ≡ x [ZMOD 25]} 1167 := by

  have h₄ {x : ℤ} (h1 : 7 * x ≡ 21 [ZMOD 14])
                  (h2 : 2 * x + 13 ≡ 16 [ZMOD 9])
                  (h3 : -2 * x + 1 ≡ x [ZMOD 25]) : x ≡ 267 [ZMOD 450] := by
    rw [Int.ModEq]
    -- Divide the first congruence by 7, remembering to divide 14 by $\text{gcf}(7,14)=7$ as well. We find that the first congruence is equivalent to $x \equiv 1\pmod{2}$.
    have h₁ {x : ℤ} (h1 : 7 * x ≡ 21 [ZMOD 14]): x ≡ 1 [ZMOD 2] := by
      rw [Int.ModEq] at h1
      simp at h1
      have : 7 * (x - 1) % 14 = 0 := by omega
      simp at this
      rcases this with ⟨k, hk⟩
      have hk: x = 2 * k + 1 := by linarith
      rw [show (1 : ℤ) = 0 + 1 by linarith, hk]
      apply Int.ModEq.add (Dvd.dvd.modEq_zero_int (Int.dvd_mul_right 2 k)) rfl
    -- Subtracting 13 from both sides and multiplying both sides by 5 (which is the modular inverse of 2, modulo 9) gives $x\equiv 6\pmod{9}$ for the second congruence.
    have h₂ {x : ℤ} (h2 : 2 * x + 13 ≡ 16 [ZMOD 9]): x ≡ 6 [ZMOD 9] := by
      rw [show (16 : ℤ) = 3 + 13 by linarith] at h2
      apply Int.ModEq.add_right_cancel' at h2
      rw [Int.ModEq] at h2
      simp at h2
      rw [Int.ModEq]
      simp
      omega
    -- Finally, adding $2x$ to both sides in the third congruence and multiplying by 17 (which is the modular inverse of 3, modulo 25) gives $x\equiv 17\pmod{25}$.
    have h₃ {x : ℤ} (h3 : -2 * x + 1 ≡ x [ZMOD 25]): x ≡ 17 [ZMOD 25] := by
      rw [Int.ModEq] at h3
      rw [Int.ModEq]
      omega
    specialize h₁ h1
    specialize h₂ h2
    specialize h₃ h3
    rw [Int.ModEq] at h₁ h₂ h₃
    -- So we want to solve  \begin{align*}
    -- x &\equiv 1 \pmod{2} \\
    -- x &\equiv 6 \pmod{9} \\
    -- x &\equiv 17 \pmod{25}. \\
    -- \end{align*}Let's first find a simultaneous solution for the second and third congruences.  We begin checking numbers which are 17 more than a multiple of 25, and we quickly find that 42 is congruent to 17 (mod 25) and 6 (mod 9). Since 42 does not satisfy the first congruence we look to the next solution $42+\text{lcm}(25,9)=267$. Now we have found a solution for the system, so we can appeal to the Chinese Remainder Theorem to conclude that the general solution of the system is $x\equiv 267 \pmod{450}$.
    omega
  -- where 450 is obtained by taking the least common multiple of 2, 9, and 25. So the least four-digit solution is $267 + 450 (2) = \boxed{1167}$.
  have : {x | 1000 ≤ x ∧ x < 10000 ∧ 7 * x ≡ 21 [ZMOD 14] ∧ 2 * x + 13 ≡ 16 [ZMOD 9] ∧ -2 * x + 1 ≡ x [ZMOD 25]} = {x | 1000 ≤ x ∧ x < 10000 ∧ x ≡ 267 [ZMOD 450]} := by
    ext n
    simp
    intro hn hn₂
    constructor
    . rintro ⟨h1, h2, h3⟩
      rw [show (-(2 * n) + 1 : ℤ) = -2 * n + 1 by linarith] at h3
      specialize h₄ h1 h2 h3
      exact h₄
    . intro h
      rw [Int.ModEq] at h
      rw [Int.ModEq, Int.ModEq, Int.ModEq]
      omega
  rw [this]
  unfold IsLeast
  have _1167_in_set: 1167 ∈ {x | 1000 ≤ x ∧ x < 10000 ∧ x ≡ 267 [ZMOD 450]} := by exact PEquiv.mem_ofSet_self_iff.mp rfl
  use _1167_in_set
  apply mem_lowerBounds.mpr
  simp
  intro x hx₁ hx₂ hx'
  rw [Int.ModEq] at hx'
  omega
