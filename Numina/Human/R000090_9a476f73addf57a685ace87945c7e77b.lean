import Mathlib

/- The greatest common divisor of a list. -/
def Fin.gcd {n} (x : Fin n → ℤ) := (Finset.univ.image x).gcd id

/- Show that the greatest common divisor (gcd) of the integers \( a_{1}, a_{2}, \ldots, a_{n} \),
  which are not all zero, is the least positive integer that can be expressed as a linear combination of
  \( a_{1}, a_{2}, \ldots, a_{n} \). -/
theorem number_theory_4524 {n} (x : Fin n → ℤ) (hx : ∃ i, x i ≠ 0) :
    IsLeast { y : ℤ | y > 0 ∧ ∃ a : Fin n → ℤ, y = ∑ i : Fin n, a i * x i} (Fin.gcd x) := by
  obtain ⟨i, hi⟩ := hx
  refine ⟨⟨?_, ?_⟩, fun y ⟨pos, ⟨a, ha⟩⟩ => ?_⟩
  -- show gcd(a1,...,an) is positive
  · have this : Fin.gcd x ∣ x i := by apply Finset.gcd_dvd; simp
    -- Because gcd(a1,..,an) divides ai which does not equal 0, we have gcd(a1,...,an) ≠ 0.
    replace := ne_zero_of_dvd_ne_zero hi this
    -- It's obvious that gcd(a1,...,an) is nonneg
    have : 0 ≤ Fin.gcd x := by
      rw [← Int.nonneg_iff_normalize_eq_self]
      apply Finset.normalize_gcd
    -- Combining above results, we know gcd(a1,...,an) is positive.
    omega
  -- show gcd(a1,...,an) is linear combination of a1,...,an
  · induction n with
    -- check base case
    | zero => simpa using i.2
    | succ n ih =>
      by_cases hj : ∃ j : Fin n, x j ≠ 0
      -- if there exists j≤n such that aj ≠ 0
      · obtain ⟨j, hj⟩ := hj
        obtain ⟨a, ha⟩ := ih (fun i => x i) j hj
        set g := Fin.gcd (fun i : Fin n => x i)
        -- gcd(a1,...,a(n+1)) = gcd(gcd(a1,...,an), a(n+1))
        have eq : Fin.gcd x = gcd g (x n) := by
          rw [gcd_comm]
          have : Finset.univ.image x = insert (x n) (Finset.univ.image fun i : Fin n => x i) := by
            ext a
            simp only [Finset.mem_image, Finset.mem_univ, true_and, Fin.exists_iff_castSucc,
              Fin.natCast_eq_last, Fin.coe_eq_castSucc, Finset.mem_insert]
            nth_rw 1 [eq_comm]
          simp only [Fin.gcd, this, g]
          apply Finset.gcd_insert
        rw [← Int.coe_gcd, Int.gcd_eq_gcd_ab] at eq
        -- use induction hypothesis
        nth_rw 1 [ha] at eq
        use fun i => if h : i = Fin.last n then g.gcdB (x n) else g.gcdA (x n) * a (i.castPred h)
        simp only [Fin.natCast_eq_last, Fin.sum_univ_castSucc,
          show ∀ i : Fin n, i.castSucc ≠ Fin.last n from
            fun _ => ne_of_lt (Fin.castSucc_lt_last _),
          ↓reduceDIte, Fin.castPred_castSucc]
        rw [eq, Finset.sum_mul, mul_comm]
        congr! 2 with i -
        · simp; ring
        · simp
        · simp
      -- otherwise, for all j≤n, aj = 0
      · simp only [ne_eq, not_exists, Decidable.not_not] at hj
        -- we must have a(n+1) ≠ 0
        -- so gcd(a1,...,an) = a(n+1) is exactly a linear combination of a1,...,a(n+1)
        have dvd : Finset.gcd {0, x n} id ∣ Fin.gcd x := by
          apply Finset.gcd_mono
          intro a ha
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha
          obtain ⟨k, hk⟩ := ha
          by_cases h : k = n
          · rw [h] at hk
            simpa [-Fin.natCast_eq_last] using .inr hk.symm
          · simp only [Fin.natCast_eq_last] at h
            have := hj (k.castPred h)
            simp only [Fin.coe_castPred, Fin.cast_val_eq_self] at this
            simpa using .inl (hk ▸ this)
        simp only [Fin.natCast_eq_last, Finset.gcd_insert, id_eq, Finset.gcd_singleton,
          normalize_apply, gcd_zero_left, normUnit_mul_normUnit, Units.val_one, mul_one,
          Units.isUnit, IsUnit.mul_right_dvd] at dvd
        obtain ⟨m, hm⟩ := dvd
        rw [mul_comm] at hm
        use fun i => if i = n then m else 0
        simpa [Fin.sum_univ_castSucc]
  -- show gcd(a1,...,an) is the least linear combination of a1,...,an
  · apply Int.le_of_dvd pos
    -- suffices to show that gcd(a1,...,an) divides any linear combination of a1,...,an
    rw [ha]
    apply Finset.dvd_sum
    rintro j -
    apply dvd_mul_of_dvd_right
    apply Finset.gcd_dvd
    simp
