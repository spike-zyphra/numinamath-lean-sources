import Mathlib

open GCDMonoid (gcd)

/- a) Show that if \( a \) and \( b \) are both even integers, which are not both zero, then \( (a, b) = 2(a / 2, b / 2) \).-/
theorem number_theory_4512_1 {a b : ℤ} (ha : Even a) (hb : Even b) (hab : a ≠ 0 ∨ b ≠ 0) :
    a.gcd b = 2 * (a / 2).gcd (b / 2) := by
  have two_mul_ediv_two (n : ℤ) : 2 * n / 2 = n := by
    rw [mul_comm]
    apply Int.mul_ediv_cancel
    norm_num
  -- exists linear combination of a,b such that gcd(a,b)=ax+by
  obtain ⟨x, y, hxy⟩ := exists_gcd_eq_mul_add_mul a b
  -- exists linear combination of a,b such that gcd(a/2,b/2)=ax/2+by/2
  obtain ⟨u, v, huv⟩ := exists_gcd_eq_mul_add_mul (a / 2) (b / 2)
  rcases ha with ⟨j, rfl⟩
  rcases hb with ⟨k, rfl⟩
  simp only [← two_mul, two_mul_ediv_two] at hxy huv ⊢
  -- gcd(a,b) | 2*gcd(a/2,b/2)
  have h1 : gcd (2*j) (2*k) ∣ 2 * gcd j k := by
    rw [huv, mul_add, ← mul_assoc, ← mul_assoc]
    apply Dvd.dvd.add
    . apply Dvd.dvd.mul_right
      apply gcd_dvd_left
    . apply Dvd.dvd.mul_right
      apply gcd_dvd_right
  -- 2*gcd(a/2,b/2) | gcd(a,b)
  have h2 : 2 * gcd j k ∣ gcd (2*j) (2*k) := by
    rw [hxy, mul_assoc, mul_assoc, ← mul_add]
    apply Int.mul_dvd_mul_left 2
    have hk : gcd j k ∣ k := gcd_dvd_right ..
    have hj : gcd j k ∣ j := gcd_dvd_left ..
    exact Dvd.dvd.add (Dvd.dvd.mul_right hj x) (Dvd.dvd.mul_right hk y)
  -- by antisymm of dvd we have gcd(a,b)=2*gcd(a/2,b/2)
  have h3 : gcd (2*j) (2*k) = 2 * gcd j k := by
    apply Int.dvd_antisymm
    . simp [gcd]
    . simp [gcd]
    . exact h1
    . exact h2
  rw [show gcd (2*j) _ = Int.gcd .. from rfl, show gcd j _ = Int.gcd .. from rfl] at h3
  exact_mod_cast h3

/- b) Show that if \( a \) is an even integer and \( b \) is an odd integer, then \( (a, b) = (a / 2, b) \).-/
theorem number_theory_4512_2 {a b : ℤ} (ha : Even a) (hb : Odd b) :
    a.gcd b = (a / 2).gcd b := by
  have two_mul_ediv_two (n : ℤ) : 2 * n / 2 = n := by
    rw [mul_comm]
    apply Int.mul_ediv_cancel
    norm_num
  -- exists linear combination of a,b such that gcd(a,b)=ax+by
  obtain ⟨x, y, hxy⟩ := exists_gcd_eq_mul_add_mul a b
  -- exists linear combination of a,b such that gcd(a/2,b/2)=ax/2+by/2
  obtain ⟨u, v, huv⟩ := exists_gcd_eq_mul_add_mul (a / 2) b
  rcases ha with ⟨j, rfl⟩
  simp only [← two_mul, two_mul_ediv_two] at hxy huv ⊢
  -- gcd(a,b) | gcd(a/2,b)
  have h1 : gcd (2*j) b ∣ gcd j b := by
    rw [huv]
    apply Dvd.dvd.add
    apply Dvd.dvd.mul_right
    refine IsCoprime.dvd_of_dvd_mul_left (?_ : IsCoprime (gcd (2*j) b) 2) ?_
    . simp [Int.coprime_iff_nat_coprime, gcd]
      apply Odd.of_dvd_nat (Odd.natAbs hb)
      have : ((2*j).gcd b : ℤ) ∣ b := Int.gcd_dvd_right
      rwa [Int.natCast_dvd] at this
    apply gcd_dvd_left
    . apply Dvd.dvd.mul_right
      apply gcd_dvd_right
  -- gcd(a/2,b) | gcd(a,b)
  have h2 : gcd j b ∣ gcd (2*j) b := by
    rw [hxy]
    apply Dvd.dvd.add
    . apply Dvd.dvd.mul_right
      apply Dvd.dvd.mul_left
      apply gcd_dvd_left
    . apply Dvd.dvd.mul_right
      apply gcd_dvd_right
  -- by antisymm of dvd we have gcd(a,b)=gcd(a/2,b)
  have h3 : gcd (2*j) b = gcd j b := by
    apply Int.dvd_antisymm
    . simp [gcd]
    . simp [gcd]
    . exact h1
    . exact h2
  rw [show gcd (2*j) _ = Int.gcd .. from rfl, show gcd j _ = Int.gcd .. from rfl] at h3
  exact_mod_cast h3
