import Mathlib

def is_special (M : Set ℕ) : Prop :=
  M.Nonempty ∧
  (∀ x ∈ M, Even x → x / 2 ∈ M) ∧
  (∀ x ∈ M, Odd x → 3 * x + 1 ∈ M)

/- A set $M$ will be called special if it simultaneously satisfies the conditions:

- it is non-empty and contains only natural numbers;
- if $x \in M$ and $x$ is even, then $\frac{x}{2} \in M$;
- if $x \in M$ and $x$ is odd, then $3 \cdot x+1 \in M$.

a) Show that if $M$ is a special set and $12 \in M$, then $M$ has at least 10 elements.

b) Show that there are infinitely many special sets that have exactly two odd elements. -/
theorem number_theory_117512 :
    (∀ M, is_special M → 12 ∈ M → 10 ≤ M.encard) ∧
    {M | is_special M ∧ ∃ x ∈ M, ∃ y ∈ M, x ≠ y ∧ Odd x ∧ Odd y ∧ ∀ z ∈ M \ {x, y}, Even z}.Infinite := by
  constructor
  . -- a) From $12 \\in M$ it follows that $M$ contains the elements $6,3,10,5,16,8,4,2,1$.
    intro M hm h12
    rcases hm with ⟨hne, heven, hodd⟩
    have h6 := heven 12 h12 (by decide)
    simp at h6
    have h3 := heven 6 h6 (by decide)
    simp at h3
    have h10 := hodd 3 h3 (by decide)
    simp at h10
    have h5 := heven 10 h10 (by decide)
    simp at h5
    have h16 := hodd 5 h5 (by decide)
    simp at h16
    have h8 := heven 16 h16 (by decide)
    simp at h8
    have h4 := heven 8 h8 (by decide)
    simp at h4
    have h2 := heven 4 h4 (by decide)
    simp at h2
    have h1 := heven 2 h2 (by decide)
    simp at h1
    let S : Finset ℕ := {12, 6, 3, 10, 5, 16, 8, 4, 2, 1}
    have : ↑S ⊆ M := by
      simp [Set.subset_def, S]
      tauto
    rw [←Set.encard_diff_add_encard_of_subset this, Set.encard_coe_eq_coe_finsetCard]
    simp [S]
  . -- b) If $n$ is a non-zero natural number, then $2^{2 n} \\equiv 1 \\pmod{3}$, so $x\_{n}=\\frac{2^{2 n}-1}{3}$ is a natural number.
    let x (n : ℕ) := (2 ^ (2 * (n + 2)) - 1) / 3
    have hpow_min : ∀ n, 4 ^ 2 ≤ 4 ^ (n + 2) := by
      intro n
      apply pow_le_pow_right'
      simp
      omega
    have hdvd : ∀ n, 3 ∣ (4 ^ (n + 2) - 1) := by
      intro n
      suffices (4 ^ (n + 2) - 1) % 3 = 0 by omega
      have := Nat.ModEq.pow (n + 2) (show 4 ≡ 1 [MOD 3] by simp [Nat.ModEq])
      simp [Nat.ModEq] at this
      omega
    have pow_4_mod_6 : ∀ n, 4 ^ (n + 1) % 6 = 4 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Nat.pow_add_one, ←Nat.mod_mul_mod, ih]
    have hx : ∀ n, Odd (x n) ∧ x n ≠ 1 := by
      intro n
      simp [x, Nat.pow_mul]
      have : 4 ^ 2 ≤ 4 ^ (n + 2) := pow_le_pow_right' (by simp) (by omega)
      constructor
      . by_contra! h
        simp at h
        apply Even.two_dvd at h
        apply Nat.mul_dvd_of_dvd_div (hdvd n) at h
        apply Nat.mod_eq_zero_of_dvd at h
        have : 4 ^ (n + 2) % 6 = 1 := by omega
        rw [pow_4_mod_6] at this
        contradiction
      . by_contra! h
        apply Nat.eq_mul_of_div_eq_left (hdvd n) at h
        simp at h
        omega
    let S (n : ℕ) := (Finset.Icc 0 (2 * (n + 2))).map ⟨(2 ^ ·), by simp [Function.Injective]⟩
    have hS : ∀ n, 1 ∈ S n ∧ ∀ x ∈ S n \ {1}, Even x := by
      intro n
      constructor
      . simp [S]
        use 0
        omega
      . simp [S]
        intro a h1 h2
        rw [even_iff_two_dvd]
        apply dvd_pow_self
        by_contra! h
        subst a
        simp at h2
    have x_nin_S : ∀ n, x n ∉ S n := by
      intro n h
      have ⟨hx1, hx2⟩ := hx n
      have ⟨hS1, hS2⟩ := hS n
      specialize hS2 (x n) ?_
      simp
      tauto
      rw [←Nat.not_odd_iff_even] at hS2
      contradiction
    -- For $n &gt; 1$, define the set $M=\\left\\{x\_{n}, 2^{2 n}, 2^{2 n-1}, 2^{2 n-2}, \\ldots, 1\\right\\}$
    let f (n : ℕ) : Set ℕ := insert (x n) (S n)
    have hSFin : ∀ n, (f n).Finite := by simp [f]
    have hf : ∀ n, (f n).ncard = 2 * n + 6 := by
      intro n
      simp [f]
      rw [show 2 * n + 6 = 2 * n + 5 + 1 by simp]
      rw [Set.ncard_eq_succ]
      use x n
      use S n
      constructor
      . simp
        apply x_nin_S
      constructor
      . rfl
      . simp
        simp [S]
        omega
    -- we obtain an infinite number of special sets that have exactly two odd elements.
    apply Set.infinite_of_injective_forall_mem (f := f)
    . simp [Function.Injective]
      intro m n h
      have : (f m).ncard = (f n).ncard := by congr
      rw [hf, hf] at this
      omega
    . intro n
      have ⟨hx1, hx2⟩ := hx n
      have ⟨hS1, hS2⟩ := hS n
      constructor
      . -- M is special
        simp [is_special]
        constructor
        . simp [f]
        constructor
        . intro z hz heven
          simp [f] at hz
          rcases hz with (hz|hz)
          . have : ¬Odd z := by simp; assumption
            subst z
            contradiction
          . rcases heven with ⟨c, hc⟩
            subst z
            ring_nf at hz
            have : (c + c) / 2 = c := by omega
            rw [this]
            simp [S] at hz
            rcases hz with ⟨a, ha1, ha2⟩
            simp [f, S]
            right
            use a - 1
            constructor
            . omega
            . rw [←Nat.two_pow_pred_mul_two] at ha2
              omega
              by_contra! h
              simp at h
              subst a
              omega
        . intro z fz hodd
          simp [f] at fz
          rcases fz with (fz | fz)
          . subst z
            simp [x]
            have : 3 * ((2 ^ (2 * (n + 2)) - 1) / 3) + 1 = 2 ^ (2 * (n + 2)) := by
              simp [x, Nat.pow_mul]
              rw [Nat.mul_div_cancel' (hdvd n)]
              have : 4 ^ 2 ≤ 4 ^ (n + 2) := pow_le_pow_right' (by simp) (by omega)
              omega
            rw [this]
            simp [f, S]
          . have : z = 1 := by
              by_contra! h
              specialize hS2 z ?_
              simp
              tauto
              rw [←Nat.not_odd_iff_even] at hS2
              contradiction
            simp [f, S]
            right
            use 2
            omega
      . -- and has exactly two odd elements: $x\_{n}$ and 1
        use 1
        constructor
        . simp [f]
          tauto
        use x n
        constructor
        . simp [f]
        constructor
        . tauto
        constructor
        . simp
        constructor
        . assumption
        . intro z hz
          simp [f] at hz
          apply hS2 z
          simp
          tauto
