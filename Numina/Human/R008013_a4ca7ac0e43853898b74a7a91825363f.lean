import Mathlib

/- Find all ordered triples $(x, y, z)$ of positive integers satisfying the equation
$$
\frac{1}{x^{2}}+\frac{y}{x z}+\frac{1}{z^{2}}=\frac{1}{2013}
$$ -/
theorem number_theory_605567 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z):
  (1 / (x ^ 2 : ℚ) + y / (x * z : ℚ) + 1 / (z ^ 2 : ℚ) = 1 / 2013) ↔
  (∃ n, 0 < n ∧ (x, y, z) = (2013 * n, 2013 * n ^ 2 - 2, 2013 * n)) := by
  constructor <;> intro h
  · -- simplify the give equation.
    replace h: x^2*z^2 = 2013*(x^2+x*y*z+z^2) := by
      field_simp at h
      norm_cast at h
      have h1: ((x*z+y*x^2)*z^2+x^2*(x*z))*2013 = (x*z) *
        (2013 * (x^2+x*y*z+z^2)) := by ring
      have h2: x^2*(x*z)*z^2 = (x*z) * (x^2*z^2) := by ring
      rw [h1, h2] at h
      apply (Nat.eq_of_mul_eq_mul_left ?_ h).symm
      apply mul_pos hx hz
    -- let d = gcd (x,z), and suppose x = da, z = db.
    set d := x.gcd z with d_def
    set a := x/d with a_def
    set b := z/d with b_def
    have x_of_da: x = d*a := by
      apply (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
    have z_of_db: z = d*b := by
      apply (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
    -- substitute x,z into the equation and simplify
    replace h: a^2*b^2*d^2 = 2013*(a^2+a*b*y+b^2) := by
      have h1: x^2*z^2 = d^2 * (a^2*b^2*d^2) := by
        rw [x_of_da, z_of_db]; ring
      have h2: 2013*(x^2+x*y*z+z^2) = d^2*(2013*(a^2+a*b*y+b^2)) := by
        rw [x_of_da, z_of_db]; ring
      rw [h1, h2] at h
      apply (Nat.eq_of_mul_eq_mul_left ?_ h)
      apply pow_pos (Nat.gcd_pos_of_pos_left z hx) _
    -- notice that a,b are coprime
    have co_ab: a.Coprime b := by
      rw [a_def, b_def, d_def]
      refine Nat.coprime_div_gcd_div_gcd ?_
      exact Nat.gcd_pos_of_pos_left z hx
    -- therefore a^2, b^2 are both coprime to a^2+aby+b^2
    have aco: a.Coprime (a^2+a*b*y+b^2) := by
      have h1: a^2+a*b*y+b^2 = a*(a+b*y) + b^2 := by ring
      have h2: a.Coprime (b^2) := Nat.Coprime.pow_right 2 co_ab
      rw [h1]
      exact (Nat.coprime_mul_left_add_right _ _ _).mpr h2
    have bco: b.Coprime (a^2+a*b*y+b^2) := by
      have h1: a^2+a*b*y+b^2 = b*(b+a*y) + a^2 := by ring
      have h2: b.Coprime (a^2) := Nat.Coprime.pow_right 2
        (Nat.coprime_comm.mp co_ab)
      rw [h1]
      apply (Nat.coprime_mul_left_add_right _ _ _).mpr h2
    -- then it must be the case a^2 ,b^2 divide 2013
    have asqdvd: a^2 ∣ 2013 := by
      have: a^2 ∣ 2013 * (a^2 + a*b*y + b^2) := by
        rw [← h, mul_assoc]
        exact Nat.dvd_mul_right _ _
      apply Nat.Coprime.dvd_of_dvd_mul_right
        (Nat.Coprime.pow_left 2 aco) this
    have bsqdvd: b^2 ∣ 2013 := by
      have: b^2 ∣ 2013 * (a^2+a*b*y+b^2) := by
        rw [← h, mul_comm (a^2) _, mul_assoc]
        apply Nat.dvd_mul_right
      apply Nat.Coprime.dvd_of_dvd_mul_right
        (Nat.Coprime.pow_left 2 bco) this
    -- since 2013 is square free, if it's divided by a square term
    -- then that square term must equal one.
    -- 2013 = 3x11x61, so it's square free.
    have sqfree_2013: Squarefree 2013 := by
      have: 2013 = 3*11*61 := by norm_num
      have h1: Squarefree (3*11) := by
        have hh1: Nat.Prime 3 := by norm_num
        have hh2: Nat.Prime 11 := by norm_num
        refine Nat.squarefree_mul_iff.mpr ⟨(by norm_num), ?_, ?_⟩
        · exact Irreducible.squarefree hh1
        · exact Irreducible.squarefree hh2
      have h2: Squarefree 61 := by
        have: Nat.Prime 61 := by norm_num
        exact Irreducible.squarefree this
      rw [this]
      refine (Nat.squarefree_mul rfl).mpr ?_
      exact ⟨h1, h2⟩
    have eqone_of_dvd{m:ℕ}(hh: m^2 ∣ 2013): m = 1 := by
      -- m^2 ∣ 2013, then m^2 can only be 1.
      have: m^2 ∣ m := by
        apply Squarefree.pow_dvd_of_pow_dvd sqfree_2013 hh
      have h1: 0 < m := by
        by_contra!
        replace: m = 0 := Nat.eq_zero_of_le_zero this
        simp [this] at hh
      have h2: m ≤ 1 := by
        have := Nat.le_of_dvd h1 this
        nth_rw 2 [← one_mul m] at this
        rw [pow_two] at this
        exact Nat.le_of_mul_le_mul_right this h1
      exact Eq.symm (Nat.le_antisymm h1 h2)
    -- then we conclude a=b=1.
    have ha: a = 1 := eqone_of_dvd asqdvd
    have hb: b = 1 := eqone_of_dvd bsqdvd
    -- then the equation simplifies to d^2 = 2013(y+2)
    replace h: d^2 = 2013 * (y+2) := by
      simp [ha, hb] at h
      simp [h]; ring
    -- 2013 is square free, so must be the case y+2 = 2013n^2 for some n
    have hy: ∃n, y = 2013*n^2 - 2 := by
      have: d ∣ (y+2) := by
        rw [pow_two] at h
        apply Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right
          sqfree_2013 (by simp only [h, dvd_refl])
      rcases this with ⟨k, hk⟩
      have hkd: d = 2013*k := by
        rw [hk, pow_two, mul_comm d k, ← mul_assoc,
        mul_comm (2013*k) _] at h
        apply Nat.eq_of_mul_eq_mul_left ?_ h
        exact Nat.gcd_pos_of_pos_left z hx
      use k
      apply Nat.eq_sub_of_add_eq
      rw [hk, hkd]; ring
    rcases hy with ⟨n, hn⟩
    -- from d^2 = 2013(y+2) and y = 2013n^2-2, we can express d in terms of n.
    have d_of_n: d = 2013*n := by
      have h1: y+2 = 2013*n^2 := by
        have: 2 ≤ 2013*n^2 := by
          rw [hn] at hy
          apply le_of_lt (Nat.lt_of_sub_pos hy)
        apply ((Nat.sub_eq_iff_eq_add this).mp hn.symm).symm
      have h2: 2013*(2013*n^2) = (2013*n)^2 := by ring
      rw [h1, h2] at h
      simp only [pow_two] at h
      apply Nat.mul_self_inj.mp h
    -- done.
    use n
    simp [d_of_n, ha, hb] at x_of_da z_of_db
    simp [x_of_da] at hx
    simp [hx, x_of_da, z_of_db, hn]
  · -- easy to verify 2013n, 2013n^2-2, 2013n satisfy the equation.
    simp at h
    rcases h with ⟨n, npos, ⟨rfl, rfl, rfl⟩ ⟩
    rw [Nat.cast_sub]; field_simp; ring
    omega