import Mathlib

open GCDMonoid (gcd)

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

theorem number_theory_4503_2 {a b c : ℤ} : Int.gcd (a+c*b) b = Int.gcd a b := by
  show Int.gcd (a + c * b) b = Int.gcd a b
  have h1 : (Int.gcd (a + c * b) b : ℤ) ∣ (Int.gcd a b : ℤ) := by
    have h3 : (Int.gcd (a + c * b) b : ℤ) ∣ (a + c * b : ℤ) := Int.gcd_dvd_left
    have h4 : (Int.gcd (a + c * b) b : ℤ) ∣ (b : ℤ) := Int.gcd_dvd_right
    have h7 : (Int.gcd (a + c * b) b : ℤ) ∣ (a : ℤ) := by
      have h5 : (Int.gcd (a + c * b) b : ℤ) ∣ (a + c * b : ℤ) := h3
      have h6 : (Int.gcd (a + c * b) b : ℤ) ∣ (c * b : ℤ) := by
        apply dvd_mul_of_dvd_right 
        exact h4 
      have h7 : (Int.gcd (a + c * b) b : ℤ) ∣ ((a + c * b : ℤ) - (c * b : ℤ)) := by
        apply Int.dvd_sub 
        assumption 
        assumption 
      have h8 : (a + c * b : ℤ) - (c * b : ℤ) = (a : ℤ) := by 
        ring 
      rw [h8] at h7 
      assumption 
    have h2 : (Int.gcd (a + c * b) b : ℤ) ∣ (Int.gcd a b : ℤ) := by
      apply Int.dvd_gcd 
      assumption 
      assumption 
    assumption 
  have h2 : (Int.gcd a b : ℤ) ∣ (Int.gcd (a + c * b) b : ℤ) := by
    have h3 : (Int.gcd a b : ℤ) ∣ (a : ℤ) := Int.gcd_dvd_left 
    have h4 : (Int.gcd a b : ℤ) ∣ (b : ℤ) := Int.gcd_dvd_right 
    have h7 : (Int.gcd a b : ℤ) ∣ (a + c * b : ℤ) := by
      have h5 : (Int.gcd a b : ℤ) ∣ (a : ℤ) := h3
      have h6 : (Int.gcd a b : ℤ) ∣ (c * b : ℤ) := by
        apply dvd_mul_of_dvd_right 
        exact h4 
      have h7 : (Int.gcd a b : ℤ) ∣ ((a : ℤ) + (c * b : ℤ)) := by
        apply Int.dvd_add 
        assumption 
        assumption 
      have h8 : (a : ℤ) + (c * b : ℤ) = (a + c * b : ℤ) := by 
        ring 
      rw [h8] at h7 
      assumption 
    have h2 : (Int.gcd a b : ℤ) ∣ (Int.gcd (a + c * b) b : ℤ) := by
      apply Int.dvd_gcd 
      assumption 
      assumption 
    assumption 
  have h3 : (Int.gcd (a + c * b) b : ℤ) = (Int.gcd a b : ℤ) := by
    apply Int.dvd_antisymm 
    all_goals tauto 
  exact_mod_cast h3