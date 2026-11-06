import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Let  $x, y$  be positive integers such that  $\frac{x^2}{y}+\frac{y^2}{x}$  is an integer. Prove that  $y|x^2$ .-/
theorem number_theory_8539 {x y : ℤ} (hxpos : 0 < x) (hypos : 0 < y)
    (hn : ∃ n : ℤ, n = x^2 / (y : ℚ) + y^2 / x) :
    y ∣ x^2 := by
  -- We have given two positive integers  $x$  and  $y$  satisfying $(1) \;\; \frac{x^2}{y} + \frac{y^2}{x} \in \mathbb{N}$ .
  rcases hn with ⟨n, hn⟩
  field_simp at hn
  norm_cast at hn
  -- Condition (1) is equivalent to $(2) \;\; xy \mid x^3 + y^3$ .
  have hxy : x*y ∣ x^3 + y^3 := by
    use n
    linear_combination -hn
  -- Let  $d=GCD(x,y)$ .  Hence there are two coprime positive integers  $a$  and  $b$  s.t.  $(x,y) = ( ad,bd)$ ,
  set d := x.gcd y with hd
  have hdx : ↑d ∣ x := Int.gcd_dvd_left
  have hdy : ↑d ∣ y := Int.gcd_dvd_right
  rcases hdx with ⟨a, ha⟩
  rcases hdy with ⟨b, hb⟩
  have hdpos : d ≠ 0 := by
      rw [← Nat.pos_iff_ne_zero, hd, Int.gcd_pos_iff]
      left
      exact hxpos.ne'
  -- which inserted in (2) result in $(3) \;\; ab \mid d(a^3 + b^3)$ .
  have hab : a*b ∣ d*(a^3+b^3) := by
    rw [ha, hb] at hxy
    obtain ⟨k, hk⟩ := hxy
    ring_nf at hk
    rw [show (d : ℤ)^3=d^2*d by ring, mul_assoc, mul_assoc, ← mul_add, mul_assoc, mul_assoc,
      mul_right_inj'] at hk
    use k
    linear_combination hk
    simp [hdpos]
  -- Now  $GCD(a^3+b^3,ab)=1$  since  $GCD(a,b)=1$ ,
  have : Int.gcd (a*b) (a^3+b^3) = 1 := by
    have : 0 < a := by
      have : 0 < d * a := by rwa [← ha]
      rw [mul_pos_iff] at this
      exact this.elim (fun h => h.2) (fun h => by
        rw [← Nat.pos_iff_ne_zero] at hdpos
        zify at hdpos
        linarith)
    have : 0 < b := by
      have : 0 < d * b := by rwa [← hb]
      rw [mul_pos_iff] at this
      exact this.elim (fun h => h.2) (fun h => by
        rw [← Nat.pos_iff_ne_zero] at hdpos
        zify at hdpos
        linarith)
    rw [Int.gcd]
    by_contra h
    rw [← Nat.coprime_iff_gcd_eq_one, Nat.Prime.not_coprime_iff_dvd] at h
    rcases h with ⟨p, hp, hpab, hpabcube⟩
    rw [Int.natAbs_mul, Nat.Prime.dvd_mul hp] at hpab
    rw [Int.natAbs_add_of_nonneg (by positivity) (by positivity),
      Int.natAbs_pow, Int.natAbs_pow] at hpabcube
    have {c d : ℕ} (hc : p ∣ c) (hcd : p ∣ c^3 + d^3) : p ∣ d := by
      suffices p ∣ d^3 from Nat.Prime.dvd_of_dvd_pow hp this
      rw [Nat.add_comm] at hcd
      have := Dvd.dvd.pow hc (show 3 ≠ 0 by norm_num)
      have := Nat.dvd_sub' hcd this
      rwa [Nat.add_sub_cancel] at this
    -- hpab : p ∣ a.natAbs ∨ p ∣ b.natAbs
    have : p ∣ a.natAbs ∧ p ∣ b.natAbs := hpab.elim
      (fun h => ⟨h, this h hpabcube⟩)
      (fun h => ⟨this h (by rwa [Nat.add_comm] at hpabcube), h⟩)
    have : p ∣ a.natAbs.gcd b.natAbs := Nat.dvd_gcd this.1 this.2
    rw [show a.natAbs.gcd b.natAbs = 1 by
      rw [← Nat.coprime_iff_gcd_eq_one]
      rw [← Nat.pos_iff_ne_zero, hd, Int.gcd] at hdpos
      have := Nat.coprime_div_gcd_div_gcd hdpos
      convert this
      . apply_fun Int.natAbs at ha
        rw [Int.natAbs_mul, Int.natAbs_cast] at ha
        nth_rw 1 [ha]
        rw [hd, Int.gcd, Nat.mul_comm, Nat.mul_div_cancel _ hdpos]
      apply_fun Int.natAbs at hb
      rw [Int.natAbs_mul, Int.natAbs_cast] at hb
      nth_rw 1 [hb]
      rw [hd, Int.gcd, Nat.mul_comm, Nat.mul_div_cancel _ hdpos]] at this
    exact Nat.Prime.not_dvd_one hp this
  -- which combined with (3) implies  $ab \mid d$ .
  have := Int.dvd_of_dvd_mul_left_of_gcd_one hab this
  -- Consequently  ${\textstyle \frac{d}{ab} = c \in \mathbb{N}}$ , i.e.  $d=abc$ .
  -- Therefore  $(x,y)=(ad,bd) = (a^2bc,ab^2c)$ ,
  -- yielding  $\frac{x^2}{y} = \frac{(a^2bc)^2}{ab^2c} = \frac{a^4b^2c^2}{ab^2c} = a^3c$ .
  rcases this with ⟨c, hc⟩
  rw [hc] at ha hb
  rw [ha, hb]
  use a^3*c
  ring
