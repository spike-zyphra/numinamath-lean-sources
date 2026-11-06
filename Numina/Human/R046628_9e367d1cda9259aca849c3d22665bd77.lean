import Mathlib

open GCDMonoid (gcd)

/- (i) The greatest common divisor of \( \frac{a}{d} \) and \( \frac{b}{d} \) is 1.-/
theorem number_theory_4503_1 {a b d : ℤ} (hdab : d = a.gcd b) (hd : d ≠ 0) :
    (a / d).gcd (b / d) = 1 := by
  -- Suppose there exists a positive integer \( e \) such that \( e \) divides \( \frac{a}{d} \) and \( e \) divides \( \frac{b}{d} \).
  set e : ℤ := ((a / d).gcd (b / d) : ℤ) with he
  have ha_eq_add : a = (a / d) * d := by
    symm
    apply Int.ediv_mul_cancel
    exact hdab ▸ Int.gcd_dvd_left
  have hb_eq_bdd : b = (b / d) * d := by
    symm
    apply Int.ediv_mul_cancel
    exact hdab ▸ Int.gcd_dvd_right
  -- This implies that there exist integers \( k \) and \( \ell \) such that \( \frac{a}{d} = ke \) and \( \frac{b}{d} = \ell e \).
  have he_dvd_ad : e ∣ a / d := Int.gcd_dvd_left
  have he_dvd_bd : e ∣ b / d := Int.gcd_dvd_right
  have hed_dvd_a : e*d ∣ a := by
    rw [ha_eq_add]
    exact Int.mul_dvd_mul he_dvd_ad (Int.dvd_refl _)
  have hed_dvd_b : e*d ∣ b := by
    rw [hb_eq_bdd]
    exact Int.mul_dvd_mul he_dvd_bd (Int.dvd_refl _)
  have hed_eq_d : e*d = d := by
    have : 0 ≤ d := by simp [hdab]
    have : 0 ≤ e := by simp [he]
    apply Int.dvd_antisymm
    . positivity
    . positivity
    nth_rw 2 [hdab]
    rw [show a.gcd b = gcd a b from rfl, dvd_gcd_iff]
    constructor <;> assumption
    exact Int.dvd_mul_left e d
  suffices e = 1 by
    rw [this, eq_comm] at he
    exact_mod_cast he
  -- Since \( d \) is the greatest common divisor of \( a \) and \( b \), it follows that \( e \) must be equal to 1.
  nth_rw 2 [← one_mul d] at hed_eq_d
  rwa [mul_left_inj' hd] at hed_eq_d

/- (ii) The greatest common divisor of \( a + cb \) and \( b \) is equal to the greatest common divisor of \( a \) and \( b \).-/
theorem number_theory_4503_2 {a b c : ℤ} : Int.gcd (a+c*b) b = Int.gcd a b := by
  suffices (Int.gcd (a+c*b) b : ℤ) = (Int.gcd a b : ℤ) by
    norm_cast at this
  apply Int.dvd_antisymm
  . positivity
  . positivity
  -- Conversely, let \( f \) be a common divisor of \( a + cb \) and \( b \). By Proposition 1.4, we can see that \( f \) divides the difference \( (a + cb) - cb = a \). Therefore, \( f \) is also a common divisor of \( a \) and \( b \).
  rw [show a.gcd b = gcd a b from rfl, dvd_gcd_iff]
  set d := (a+c*b).gcd b
  have hd_dvd_acb : ↑d ∣ a+c*b := Int.gcd_dvd_left
  have hd_dvd_b : ↑d ∣ b := Int.gcd_dvd_right
  refine ⟨?_, hd_dvd_b⟩
  rw [show a = a+c*b-c*b by ring]
  apply Dvd.dvd.sub
  . assumption
  . apply Dvd.dvd.mul_left
    assumption
  -- By Proposition 1.4, since \( e \) divides both \( a \) and \( b \), it follows that \( e \) also divides \( a + cb \). Thus, \( e \) is a common divisor of \( a + cb \) and \( b \).
  rw [show (a+c*b).gcd b = gcd (a+c*b) b from rfl, dvd_gcd_iff]
  constructor
  . apply Dvd.dvd.add
    . exact Int.gcd_dvd_left
    . apply Dvd.dvd.mul_left
      exact Int.gcd_dvd_right
  . exact Int.gcd_dvd_right
