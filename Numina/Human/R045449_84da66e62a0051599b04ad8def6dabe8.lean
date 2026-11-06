import Mathlib

/- Let $x, y, z$ be positive integers that have no common divisor greater than 1, and satisfy the equation


$$

\frac{1}{x}+\frac{1}{y}=\frac{1}{z}

$$


Prove that $x-z, y-z$, and $y+x$ are perfect squares. -/
theorem number_theory_151634 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : Nat.Coprime x y) (hyz : Nat.Coprime y z) (hzz : Nat.Coprime x z)
    (h : (1 / x : ℚ) + 1 / y = 1 / z) :
    IsSquare (x - z) ∧ IsSquare (y - z) ∧ IsSquare (y + x) := by
  -- first prove x > z and y > z as that'll allow us to easily work between natural and integers
  have aux {x y z : ℕ} (hx: 0 < x) (hy: 0 < y) (hz : 0 < z) (h : (1 / x : ℚ) + 1 / y = 1 / z) : z < x := by
    have : 1/(x:ℚ) < 1/z := by linarith [show 0 < 1/(y:ℚ) by simp [hy]]
    suffices (z:ℚ) < x by norm_cast at this
    apply lt_of_one_div_lt_one_div
    norm_cast; assumption
  have hxz' : x > z := aux hx hy hz h
  have hyz' : y > z := by
    apply aux hy hx hz
    rw [add_comm] at h
    exact h
  have hxz'' : (x - z: ℤ) = ↑(x - z) := by omega
  have hyz'' : (y - z: ℤ) = ↑(y - z) := by omega
  -- next convert the equation to (x-z)(y-z) = z^2
  replace h : (x - z : ℚ) * (y - z) = z^2 := by
    field_simp at h
    linarith
  replace h : (x - z : ℤ) * (y - z : ℤ) = z^2 := by
    norm_cast at h ⊢
  -- prove x-z and y-z are coprime
  have hxyz_coprime : Nat.Coprime (x - z) (y - z) := by
    -- note that prime k dividing x-z implies it divides z^2, hence z
    apply Nat.coprime_of_dvd
    rintro k hpk hkxz
    have : k ∣ z^2 := by calc
      k ∣ (x - z) * (y - z) := by exact Dvd.dvd.mul_right hkxz (y - z)
      _ = z^2 := by
        rw [hxz'', hyz''] at h
        norm_cast at h
    have : k ∣ z := by exact Nat.Prime.dvd_of_dvd_pow hpk this
    -- then k divides x
    have : k ∣ (x - z) + z := by exact (Nat.dvd_add_iff_right hkxz).mp this
    have : k ∣ x := by
      rw [show (x - z) + z = x by omega] at this
      exact this
    -- but this contradicts coprimality of x and z
    have : ¬ Nat.Coprime x z := by
      refine Nat.not_coprime_of_dvd_of_dvd ?_ ‹k ∣ x› ‹k ∣ z›
      exact Nat.Prime.one_lt hpk
    contradiction
  -- convert the coprimality to integer coprimality
  replace hxyz_coprime : IsCoprime (x - z : ℤ) (y - z : ℤ) := by
    apply Int.coprime_iff_nat_coprime.mpr
    rw [hxz'', hyz'']
    norm_cast
  -- coprimeness of x-z and y-z means both are squares
  replace aux {x y z : ℕ} (hxyz_coprime : IsCoprime (x - z : ℤ) (y - z : ℤ)) (hxz : z < x) (h: (x - z : ℤ) * (y - z) = z ^ 2) : IsSquare (x - z) := by
    have : ∃ a : ℤ, x - z = a ^ 2 ∨ x - z = -a ^ 2 := Int.sq_of_coprime hxyz_coprime h
    obtain ⟨a, hsq⟩ := this
    use a.natAbs
    suffices x - z = a^2 by
      rw [← Int.natAbs_sq, show (x - z:ℤ) = ↑(x - z) by omega] at this
      norm_cast at this
      linarith
    apply Or.resolve_right hsq
    by_contra h
    have := calc
      (0:ℤ) < x - z := by omega
      _ ≤ 0 := by rw [h]; simp; positivity
    linarith
  have ht1 : IsSquare (x - z) := by exact aux hxyz_coprime hxz' h
  have ht2 : IsSquare (y - z) := by
    apply aux hxyz_coprime.symm hyz'
    rw [mul_comm]
    assumption
  simp [ht1, ht2]
  clear * - h ht1 ht2 hxz' hyz' hxz'' hyz''
  -- now a^2 = (x-z), b^2 = (y-z), then ab = z
  replace h : (x - z) * (y - z) = z^2 := by
    rw [hxz'', hyz''] at h
    exact_mod_cast h
  obtain ⟨a, ha⟩ := ht1
  obtain ⟨b, hb⟩ := ht2
  have habz : (a * b)^2 = z^2 := by
    rw [← h, ha, hb]
    ring
  simp at habz
  -- finally y + x can then be written as (a+b)^2 and we're done
  rw [show y + x = (y - z) + 2 * z + (x - z) by omega]
  rw [ha, hb, ← habz]
  use a + b
  ring