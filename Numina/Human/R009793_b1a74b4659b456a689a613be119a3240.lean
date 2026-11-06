import Mathlib

/- There are $24$ different complex numbers $z$ such that $z^{24} = 1$. For how many of these is $z^6$ a real number?
(A) 0  (B) 4  (C) 6  (D) 12 (E) 24 -/
theorem algebra_97509 : {z : ℂ | z ^ 24 = 1 ∧ (z ^ 6).im = 0}.ncard = 12 := by
  -- The roots of unity of order $24 are in bijection with natural numbers $n < 24$ via
  -- $z = e^{2\pi i n / 24}$. However, note that $z^6$ is real iff $n$ is even:
  have pow_six_real_iff (n : ℕ) : (Complex.exp (2 * Real.pi * Complex.I * (n / 24)) ^ 6).im = 0 ↔ 2 ∣ n := by
    simp [← Complex.exp_nat_mul]
    ring_nf
    have : (Complex.exp (Complex.ofReal (Real.pi * n * (1 / 2)) * Complex.I)).im = Real.sin (Real.pi * n * (1 / 2)) := Complex.exp_ofReal_mul_I_im (Real.pi * n * (1 / 2))
    push_cast at this
    move_mul [Complex.I]
    rw [this, Real.sin_eq_zero_iff]
    move_mul [Real.pi]
    simp [Real.pi_ne_zero]
    field_simp
    constructor
    . intro h
      rcases h with ⟨k, hk⟩
      norm_cast at hk
      use k.natAbs
      omega
    . intro h2n
      rcases h2n with ⟨k, hk⟩
      use k
      rw [hk]
      push_cast
      ring_nf

  -- So we can divide $n$ by 2 and count the number of natural numbers less than 12,
  -- and use that for the domain of the bijection.
  let S := {z : ℂ | z ^ 24 = 1 ∧ (z ^ 6).im = 0}
  let T := Finset.range 12
  let f : ℕ → ℂ := fun n => Complex.exp (2 * Real.pi * Complex.I * (n / 12))

  -- Our function is injective when restricted to $k < 12$ because it is within one period of $f$.
  have hfinj: Set.InjOn f T := by
    intro n1 hn1 n2 hn2 h
    simp [T] at hn1 hn2
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
    have : (2 * Real.pi * Complex.I) * (n1 / 12) = (2 * Real.pi * Complex.I) * (k + n2 / 12) := by
      rw [hk]
      ring_nf
    field_simp [Complex.two_pi_I_ne_zero] at this
    have : ((n1 : ℤ) : ℂ) = ((k * 12 + n2 : ℤ) : ℂ) := by push_cast; exact this
    have : n1 = k * 12 + n2 := Int.cast_inj.mp this
    omega

  have hfimage: S = f '' T := by
    ext z
    simp [S, T]
    constructor
    . -- Here, given a $z$ in $S$, we need to recover $n$.
      intro h
      rcases h with ⟨hz1, hzr⟩
      -- With some setup, we can use Mathlib's result on roots of unity to show
      -- $z$ must be of the form $e^{2\pi i n / 24}$.
      have : z ≠ 0 := by
        intro hz
        rw [hz] at hz1
        simp at hz1
      let z' : ℂˣ := Units.mk0 z this
      have : (z' : ℂ) ∈ Polynomial.nthRoots 24 1 := by
        rw [Polynomial.mem_nthRoots (by norm_num)]
        exact hz1
      have : z' ∈ rootsOfUnity 24 ℂ := by
        rw [mem_rootsOfUnity_iff_mem_nthRoots];
        exact this
      obtain ⟨n, hn, hiz⟩ := (Complex.mem_rootsOfUnity 24 z').mp this
      rw [Units.val_mk0] at hiz
      rw [← hiz] at hzr
      -- Using the result above, we can show that $n$ is even, and thus
      -- get a natural number $i < 12$ as required.
      obtain ⟨i', hi'⟩ := (pow_six_real_iff n).mp hzr
      use i'
      and_intros
      . omega
      . field_simp [f]
        ring_nf
        rw [hi'] at hiz
        push_cast at hiz
        ring_nf at hiz
        rw [hiz]
    . -- Here, some calculation shows that $f(i)$ is indeed in $S$.
      intro h
      rcases h with ⟨i, hi, hiz⟩
      simp [← hiz, f]
      and_intros
      . rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
        use 2 * i
        field_simp
        ring_nf
      . have : (Complex.exp (2 * Real.pi * Complex.I * ((2 * i : ℕ) / 24)) ^ 6).im = 0 := (pow_six_real_iff (2 * i)).mpr (by omega)
        push_cast at this
        ring_nf at this
        ring_nf
        exact this

  -- Since $f$ restricts to a bijection between $S$ and $T$,
  -- the cardinalities of the two sets are the same, namely $12$.
  calc
    S.ncard = Nat.card S := by rw [Set.Nat.card_coe_set_eq]
    _ = Nat.card (f '' T) := by rw [hfimage]
    _ = Nat.card T := by exact Nat.card_image_of_injOn hfinj
    _ = Finset.card T := by rw [Nat.card_eq_finsetCard]
    _ = 12 := by simp [T]