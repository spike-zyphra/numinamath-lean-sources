import Mathlib

/-What is the product of all constants $k$ such that the quadratic $x^2 + kx +15$ can be factored in the form $(x+a)(x+b)$, where $a$ and $b$ are integers?-/
theorem algebra_20919 :
    ∃ (S : Finset ℤ), S = {k | ∃ (a b : ℤ), ∀x, x^2 + k * x + 15 = (x + a) * (x + b)} ∧
    ∏ i ∈ S, i = 16384 := by
  use {16, 8, -16, -8}
  constructor
  · ext k
    simp
    constructor
    · rintro (r | r | r | r)
      · -- k = 16
        use 1
        use 15
        rw [r]
        ring_nf
        simp
      · -- k = 8
        use 3
        use 5
        rw [r]
        ring_nf
        simp
      · -- k = -16
        use -1
        use -15
        rw [r]
        ring_nf
        simp
      · -- k = -8
        use -3
        use -5
        rw [r]
        ring_nf
        simp
    · rintro ⟨a, b, hab₁⟩
      -- If $x^2 + kx + 15= (x+a)(x+b)$, then \[x^2 + kx + 15 = x^2 + ax +bx +ab = x^2 +(a+b)x + ab.\]
      -- Therefore, we must have $ab = 15$,
      have hab₂ : a * b = 15 := by
        specialize hab₁ 0
        simp at hab₁
        exact hab₁.symm
      -- and for any such $a$ and $b$, we have $k = a+b$.
      have hab₃ : a + b = k := by
        specialize hab₁ 1
        ring_nf at hab₁
        rw [hab₂] at hab₁
        linarith
      rw [hab₃.symm]
      -- There are four pairs of integers that multiply to 15.  They are 1 and 15 (which give $k=16$), 3 and 5 (which give $k=8$), $-1$ and $-15$ (which gives $k=-16$), and -3 and -5 (which give $k=-8$).  The product of these four possible values of $k$ is \begin{align*}
      -- (16)(8)(-16)(-8)& = (2^4)(2^3)(-2^4)(-2^3)\\
      -- & = 2^{4+3+4+3} \\&= 2^{14}\\& = 2^{10}\cdot 2^4 = (1024)(16) = \boxed{16384}.
      -- \end{align*}
      have mem_15_divisors {n m : ℕ} (hnm : n * m = 15) :
          n ∈ (15 : ℕ).divisors := by
        apply Nat.mem_divisors.mpr
        simp
        rw [hnm.symm]
        simp
      rw [show (15 : ℕ).divisors = {1, 3, 5, 15} by rfl] at mem_15_divisors
      simp at mem_15_divisors
      by_cases h₀: 0 < a
      · obtain ⟨n, hn⟩ := show ∃(n : ℕ), a = n by
          use a.toNat
          refine Eq.symm (Int.toNat_of_nonneg ?_)
          linarith
        have : 0 < b := by
          have : 0 < a * b := by rw [hab₂]; linarith
          exact (pos_iff_pos_of_mul_pos this).mp h₀
        obtain ⟨m, hm⟩ := show ∃(m : ℕ), b = m by
          use b.toNat
          refine Eq.symm (Int.toNat_of_nonneg ?_)
          linarith
        rw [hn, hm] at hab₂
        rw [hn, hm]
        norm_cast at hab₂
        norm_cast
        simp
        obtain (r | r | r | r) := mem_15_divisors hab₂
        repeat rw [r] at hab₂; omega
      simp at h₀
      obtain ⟨n, hn⟩ := show ∃(n : ℕ), -a = n by
        use (-a).toNat
        refine Eq.symm (Int.toNat_of_nonneg ?_)
        linarith
      obtain ⟨m, hm⟩ := show ∃(m : ℕ), -b = m by
        use (-b).toNat
        refine Eq.symm (Int.toNat_of_nonneg ?_)
        have : 0 ≤ a * b := by rw [hab₂]; linarith
        obtain (⟨r₁, r₂⟩ | ⟨r₁, r₂⟩) := Int.nonneg_or_nonpos_of_mul_nonneg this
        · have : a = 0 := by linarith
          rw [this] at hab₂
          linarith
        · linarith
      rw [show a * b = (-a) * (-b) by ring_nf] at hab₂
      rw [hn, hm] at hab₂
      norm_cast at hab₂
      rw [show a + b = -((-a) + (-b)) by ring_nf, neg_eq_iff_eq_neg, neg_eq_iff_eq_neg, neg_eq_iff_eq_neg, neg_eq_iff_eq_neg]
      rw [hn, hm]
      norm_cast
      simp
      norm_cast
      obtain (r | r | r | r) := mem_15_divisors hab₂
      repeat rw [r] at hab₂; omega
  · norm_num
