import Mathlib

/- Let  $p$  be an odd prime.Positive integers  $a,b,c,d$  are less than  $p$ ,
  and satisfy  $p|a^2+b^2$  and  $p|c^2+d^2$ .
  Prove that exactly one of  $ac+bd$  and  $ad+bc$  is divisible by  $p$-/
theorem number_theory_8619
  (p : ℕ)
  (a b c d : ℤ)
  (h : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d )
  (h₀ : Odd p)
  (h₁ : Nat.Prime p)
  (h₂ : a < p)
  (h₃ : b < p)
  (h₄ : c < p)
  (h₅ : d < p)
  (h₆ : (p : ℤ)∣ a^2 + b^2)
  (h₇ : (p : ℤ)∣ c^2 + d^2) :
  ((p : ℤ) ∣ a * c + b * d ∧ ¬(p : ℤ) ∣ a * d + b * c) ∨ (¬(p : ℤ) ∣ a * c + b * d ∧ (p : ℤ) ∣ a * d + b * c) := by
    --  Consider the difference \( (ac + bd) - (ad + bc) \):
    --  \[
    --  (ac + bd) - (ad + bc) = ac + bd - ad - bc = (a - b)(c - d)
    --  \]
    have h1 : a * c + b * d - (a * d + b * c) = (a - b) * (c - d) := by linarith
    -- Since \( a, b, c, d \) are all less than \( p \), \( a \not\equiv b \pmod{p} \) and \( c \not\equiv d \pmod{p} \)
    --(otherwise \( a^2 + b^2 \) and \( c^2 + d^2 \) would not be zero modulo \( p \)).
    have aux : ∀ (a b p : ℤ), 0 < a → a < p → 0 < b → b < p → p ∣ a^2 + b^2 → Prime p → Odd p →
     ¬ p ∣ a - b := by
      intro a b p h1 h2 h3 h4 h7 h8 h9 h5
      have h2 : a = b := by
        have : (a - b).natAbs < p.natAbs := by
          have : |a - b| < p := abs_sub_lt_of_nonneg_of_lt (le_of_lt h1) h2 (le_of_lt h3) h4
          rw [Int.abs_eq_natAbs] at this
          have h6 : p.natAbs = p := Int.natAbs_of_nonneg (by linarith)
          rw [←h6] at this
          norm_cast at this
        have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h5 this
        linarith
      rw [h2] at h7
      have : p ∣ b := by
        have : p ∣ 2 * b ^ 2 := by convert h7 using 1; ring
        have := (Prime.dvd_mul h8).1 this
        have tmp : ¬p ∣ 2 := fun hh => by
          have := Int.le_of_dvd (by linarith) hh
          have : 0 < p := by linarith
          interval_cases p
          . exact not_prime_one h8
          · tauto
        have := (or_iff_right tmp).1 this
        rw [pow_two] at this
        have := (Prime.dvd_mul h8).1 this
        tauto
      have := Int.le_of_dvd h3 this
      linarith
    have h2 := aux a b p h.1 h₂ h.2.1 h₃ h₆ (Nat.prime_iff_prime_int.mp h₁) ((Int.odd_coe_nat p).mpr h₀)
    have h3 := aux c d p h.2.2.1 h₄ h.2.2.2 h₅ h₇ (Nat.prime_iff_prime_int.mp h₁) ((Int.odd_coe_nat p).mpr h₀)
    -- If \( (a - b)(c - d) \not\equiv 0 \pmod{p} \), then \( p \) does not divide \( (ac + bd) - (ad + bc) \).
    have h4 : ¬ (p : ℤ)∣ (a - b) * (c - d) := by
      intro h4
      have := Int.Prime.dvd_mul' h₁ h4
      tauto
    -- This implies that \( p \) cannot divide both \( ac + bd \) and \( ad + bc \) simultaneously.
    replace h4 : ¬ (p : ℤ)∣ a * c + b * d - (a * d + b * c) := by simpa [h1]
    have h5 : (p : ℤ) ∣ (a * c + b * d) * (a * d + b * c) := by
      -- Consider the product \( (ac + bd)(ad + bc) \):
    --  \[
    --  (ac + bd)(ad + bc) = a^2cd + abcd + abcd + b^2cd = cd(a^2 + b^2) + ab(c^2 + d^2)
    --  \]
      have h5 : (a * c + b * d) * (a * d + b * c) = c * d * (a^2 + b^2) + a * b * (c^2 + d^2) := by
        linarith
      --  Therefore, \( (ac + bd)(ad + bc) \equiv 0 \pmod{p} \).
      rw [h5]
      exact Int.dvd_add (dvd_mul_of_dvd_right h₆ _) (dvd_mul_of_dvd_right h₇ _)
    --  Since \( (ac + bd)(ad + bc) \equiv 0 \pmod{p} \) and \( p \) does not divide both
    --  \( ac + bd \) and \( ad + bc \) simultaneously, it follows that exactly one of
    --  \( ac + bd \) and \( ad + bc \) must be divisible by \( p \).
    replace h5 := Int.Prime.dvd_mul' h₁ h5
    rcases h5 with hl | hr
    · exact Or.inl ⟨hl, fun h6 => h4 (Int.dvd_sub hl h6)⟩
    · exact Or.inr ⟨fun h6 => h4 (Int.dvd_sub h6 hr), hr⟩
