import Mathlib

open Int

lemma Int.dvd_iff {a b m : ℤ} (h : a ≡ b [ZMOD m]) (hdm : d ∣ m) : d ∣ a ↔ d ∣ b := by
  simp only [← Int.modEq_zero_iff_dvd]
  replace h := h.of_dvd hdm
  exact ⟨h.symm.trans, h.trans⟩

/-
Show that if \( a, b, \) and \( c \) are integers with \( c > 0 \) such that \( a \equiv b \pmod{c} \), then \( (a, c) = (b, c) \).
-/
theorem number_theory_4656 {a b c : ℤ} (_ : 0 < c) : a ≡ b [ZMOD c] → a.gcd c = b.gcd c := by
  intro h
  -- First, we have that the $\gcd(a,c)\mid c$.
  have h1 := gcd_dvd_right a c
  -- Similarly, the gcd of $\gcd(b,c)\mid c$.
  have h2 := gcd_dvd_right b c
  -- Then, $\gcd(a,c) \mid \gcd(b,c)$.
  have h' : _ := (Int.dvd_gcd ((Int.dvd_iff h h1).mp Int.gcd_dvd_left) h1)
  -- Similarly, $\gcd(b,c) \mid \gcd(a,c)$.
  have h'' : _ := (Int.dvd_gcd ((Int.dvd_iff h  h2).mpr Int.gcd_dvd_left) h2)
  -- We have $0 \le \gcd(a,c)$ and $0 \le \gcd(b,c)$.
  have hp1 : (0 : ℤ) ≤ a.gcd c := by nlinarith
  have hp2 : (0 : ℤ) ≤ b.gcd c := by nlinarith
  -- so $\gcd(a,c) = \gcd(b,c)$.
  have : _ := (Int.dvd_antisymm hp1 hp2) h' h''
  aesop
