import Mathlib

/-
What can you conclude if \( a^{2} \equiv b^{2} \mod p \), where \( a \) and \( b \) are integers and \( p \) is a prime number?
-/
theorem number_theory_4664 {a b p : ℤ} (hp : Prime p) : a^2 ≡ b^2 [ZMOD p] → a ≡ b [ZMOD p] ∨ a ≡ -b [ZMOD p] := by
  intro h
  -- We have $p\mid (a^2-b^2)$ because $a^2\equiv b^2\pmod p$
  have : _ := Int.ModEq.dvd <| Int.ModEq.symm h
  -- This can be rewritten as $p\mid (a+b)*(a-b)$
  rw [(show a^2 - b^2 = (a + b)*(a -b) by ring)] at this
  -- Because $p$ is prime, $p\mid a+b$ or $p\mid a-b$
  cases (Prime.dvd_or_dvd hp this) with
  | inl h =>
    -- Consider $p\mid a+b$.
    -- It is easy to get that $a\equiv -b\pmod{a+b}$
    have h' : a ≡ -b [ZMOD a+b] := by
      have : a+b ≡ 0 [ZMOD a+b] := Dvd.dvd.modEq_zero_int (dvd_refl _)
      have : a ≡ -b [ZMOD a+b] := by
        have : _ :=  Int.ModEq.add_right (-b) this
        simp_all
      exact this
    right
    -- Because $p\mid a+b$, we can conclude that $a\equiv -b\pmod{p}$
    apply Int.ModEq.of_dvd h h'
  | inr h =>
    -- Consider $p\mid a-b$.
    -- Similarly, $a\equiv b\pmod{a-b}$
    have h' : a ≡ b [ZMOD (a-b)] := by
      have : a-b ≡ 0 [ZMOD a-b] := Dvd.dvd.modEq_zero_int (dvd_refl _)
      have : a ≡ b [ZMOD a-b] := by
        have : _ :=  Int.ModEq.add_right b this
        simp_all
      exact this
    left
    -- Because $p\mid a-b$, we can conclude that $a\equiv b\pmod{p}$
    apply Int.ModEq.of_dvd h h'
