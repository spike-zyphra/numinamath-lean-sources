import Mathlib
set_option maxRecDepth 10000000
set_option maxHeartbeats 10000000

/-Find the number of distinct numbers in the list
\[\left\lfloor \frac{1^2}{1000} \right\rfloor, \ \left\lfloor \frac{2^2}{1000} \right\rfloor, \ \left\lfloor \frac{3^2}{1000} \right\rfloor, \ \dots, \ \left\lfloor \frac{1000^2}{1000} \right\rfloor.\]-/
theorem algebra_11565 : {x | ∃(n : ℕ), 1 ≤ n ∧ n ≤ 1000 ∧ x = ⌊(n : ℝ)^2 / 1000⌋.toNat}.ncard = 751 := by
  -- Let $n$ be a positive integer. Then \frac{(n + 1)^2}{1000} - \frac{n^2}{1000} = \frac{2n + 1}{1000}.
  -- Thus, the inequality $\frac{(n + 1)^2}{1000} - \frac{n^2}{1000} < 1$ is equivalent to
  -- \frac{2n + 1}{1000} < 1, or $n < 499 + \frac{1}{2}.$

  -- Prove that $Set$ is the union of two sets.
  have hSet_union : {x | ∃(n : ℕ), 1 ≤ n ∧ n ≤ 1000 ∧ x = ⌊(n : ℝ)^2 / 1000⌋.toNat} =
                    {x | ∃(n : ℕ), 1 ≤ n ∧ n ≤ 500 ∧ x = ⌊(n : ℝ)^2 / 1000⌋.toNat} ∪
                    {x | ∃(n : ℕ), 501 ≤ n ∧ n ≤ 1000 ∧ x = ⌊(n : ℝ)^2 / 1000⌋.toNat} := by
    ext x
    simp
    constructor
    . -- x ∈ {x | ∃ n, 1 ≤ n ∧ n ≤ 1000 ∧ x = (n ^ 2 / 1000).toNat} → x ∈ {x | ∃ n, 1 ≤ n ∧ n ≤ 500 ∧ x = (n ^ 2 / 1000).toNat} ∪ {x | ∃ n, 501 ≤ n ∧ n ≤ 1000 ∧ x = (n ^ 2 / 1000).toNat}
      intro hx
      rcases hx with ⟨n, hn⟩
      by_cases hleq : n ≤ 500
      . apply Or.inl
        use n
        use hn.1
        use hleq
        use hn.2.2
      simp at hleq
      apply Or.inr
      use n
      use (by linarith)
      use hn.2.1
      use hn.2.2
    . -- x ∈ {x | ∃ n, 1 ≤ n ∧ n ≤ 500 ∧ x = (n ^ 2 / 1000).toNat} ∪ {x | ∃ n, 501 ≤ n ∧ n ≤ 1000 ∧ x = (n ^ 2 / 1000).toNat} → x ∈ {x | ∃ n, 1 ≤ n ∧ n ≤ 1000 ∧ x = (n ^ 2 / 1000).toNat}
      intro hx
      rcases hx with (hx | hx)
      . rcases hx with ⟨n, hn⟩
        use n
        repeat use (by linarith)
      . rcases hx with ⟨n, hn⟩
        use n
        repeat use (by linarith)

  have hSet_finite : {x | ∃ (n : ℕ), 1 ≤ n ∧ n ≤ 1000 ∧ x = ⌊(n : ℝ)^2 / 1000⌋.toNat}.Finite := by
    have : {x | ∃ (n : ℕ), 1 ≤ n ∧ n ≤ 1000 ∧ x = ⌊(n : ℝ)^2 / 1000⌋.toNat} ⊆ {x | x ≤ 1000} := by
      simp
      intro x n hn₁ hn₂ hn₃
      rw [hn₃]
      have q : n ^ 2 / (1000 : ℝ) ≤ 1000^2 / (1000 : ℝ) := by
        rw [div_le_div_iff]
        field_simp
        norm_cast
        exact Nat.pow_le_pow_of_le_left hn₂ 2
        repeat positivity
      rw [pow_two 1000, ←mul_div, div_self (by positivity), mul_one] at q
      have p : ⌊n ^ 2 / (1000 : ℝ)⌋ ≤ (1000 : ℝ) := by
        apply le_trans
        case b => exact (n ^ 2 / (1000 : ℝ))
        apply Int.floor_le
        linarith
      apply Int.toNat_le.mpr
      norm_cast at p
      norm_cast
    have h_finite : {x | x ≤ 1000}.Finite := by exact Set.finite_le_nat 1000
    exact Set.Finite.subset h_finite this

  have a_finite : {x | ∃(n : ℕ), 1 ≤ n ∧ n ≤ 500 ∧ x = ⌊(n : ℝ)^2 / 1000⌋.toNat}.Finite := by
    apply Set.Finite.subset hSet_finite
    rw [hSet_union]
    apply Set.subset_union_left
  have b_finite : {x | ∃(n : ℕ), 501 ≤ n ∧ n ≤ 1000 ∧ x = ⌊(n : ℝ)^2 / 1000⌋.toNat}.Finite := by
    apply Set.Finite.subset hSet_finite
    rw [hSet_union]
    apply Set.subset_union_right
  have disjoint_a_b : Disjoint {x | ∃(n : ℕ), 1 ≤ n ∧ n ≤ 500 ∧ x = ⌊(n : ℝ)^2 / 1000⌋.toNat}
                    {x | ∃(n : ℕ), 501 ≤ n ∧ n ≤ 1000 ∧ x = ⌊(n : ℝ)^2 / 1000⌋.toNat} := by
    apply Set.disjoint_iff_forall_ne.mpr
    simp
    intro x n hn hn' hx
    have hx: x ≤ 250 := by
      rw [hx]
      have q : n ^ 2 / (1000 : ℝ) ≤ 500^2 / (1000 : ℝ) := by
        rw [div_le_div_iff]
        field_simp
        norm_cast
        exact Nat.pow_le_pow_of_le_left hn' 2
        repeat positivity
      norm_num at q
      have p : ⌊n ^ 2 / (1000 : ℝ)⌋ ≤ (250 : ℝ) := by
        apply le_trans
        case b => exact (n ^ 2 / (1000 : ℝ))
        apply Int.floor_le
        linarith
      apply Int.toNat_le.mpr
      norm_cast at p
      norm_cast
    intro y m hm hm' hy
    have hy: 251 ≤ y := by
      rw [hy]
      have q : 501^2 / (1000 : ℝ) ≤ m ^ 2 / (1000 : ℝ) := by
        rw [div_le_div_iff]
        field_simp
        norm_cast
        exact Nat.pow_le_pow_of_le_left hm 2
        repeat positivity
      norm_num at q
      have p : 251 ≤ ⌊m ^ 2 / (1000 : ℝ)⌋ := by
        apply Int.le_floor.mpr
        norm_cast
        norm_cast at q
        linarith
      apply (Int.le_toNat (by linarith)).mpr
      exact p
    intro hxy
    rw [hxy] at hx
    linarith

  rw [hSet_union, Set.ncard_union_eq disjoint_a_b a_finite b_finite]
  -- Hence, for $n \le 499,$ the difference between $\frac{n^2}{1000}$ and $\frac{(n + 1)^2}{1000}$ is less than 1, which means the list \[\left\lfloor \frac{1^2}{1000} \right\rfloor, \ \left\lfloor \frac{2^2}{1000} \right\rfloor, \ \left\lfloor \frac{3^2}{1000} \right\rfloor, \ \dots, \ \left\lfloor \frac{500^2}{1000} \right\rfloor\]includes all the numbers from 0 to $\left\lfloor \frac{500^2}{1000} \right\rfloor = 250.$
  have a_ncard : {x | ∃ (n : ℕ), 1 ≤ n ∧ n ≤ 500 ∧ x = ⌊↑n ^ 2 / (1000 : ℝ)⌋.toNat}.ncard = 251 := by
    have : {x | ∃ (n : ℕ), 1 ≤ n ∧ n ≤ 500 ∧ x = ⌊↑n ^ 2 / (1000 : ℝ)⌋.toNat} = {x | x ≤ 250} := by
      ext x
      simp
      have : ∃(f : ℕ → ℤ), ∀n, f n = (⌊n^2 / (1000 : ℝ)⌋.toNat : ℤ) := by
        use fun n => ⌊n^2 / (1000 : ℝ)⌋.toNat
        simp
      rcases this with ⟨f, hf⟩
      constructor
      . -- (∃ n, 1 ≤ n ∧ n ≤ 500 ∧ x = ⌊n ^ 2 / 1000⌋.toNat) → x ≤ 250
        intro h
        rcases h with ⟨n, ⟨hn₁, hn', hx⟩⟩
        rw [hx]
        have q : n ^ 2 / (1000 : ℝ) ≤ 500^2 / (1000 : ℝ) := by
          rw [div_le_div_iff]
          field_simp
          norm_cast
          exact Nat.pow_le_pow_of_le_left hn' 2
          repeat positivity
        norm_num at q
        have p : ⌊n ^ 2 / (1000 : ℝ)⌋ ≤ (250 : ℝ) := by
          apply le_trans
          case b => exact (n ^ 2 / (1000 : ℝ))
          apply Int.floor_le
          linarith
        apply Int.toNat_le.mpr
        rw [← Int.lt_add_one_iff , Int.floor_lt]
        apply lt_of_le_of_lt
        exact q
        norm_num
      . -- x ≤ 250 → ∃ n, 1 ≤ n ∧ n ≤ 500 ∧ x = ⌊n ^ 2 / 1000⌋.toNat
        have hn (n : ℕ) (hn' : n ≤ 499) : ((n + 1)^2 / (1000 : ℝ)) - (n^2 / (1000 : ℝ)) < 1 := by
          have : (n + 1: ℝ) ^ 2 - n^2 = 2 * n + 1 := by linarith
          field_simp
          rw [this, div_lt_one (by positivity)]
          norm_cast
          linarith

        have hn (n : ℕ) (h₂ : n ≤ 500) : f (n + 1) - f n ≤ 1 ∧ 0 ≤ f (n + 1) - f n := by
          rw [hf (n + 1), hf n]
          have : ⌊(n + 1 : ℕ)^2 / (1000 : ℝ)⌋.toNat = ⌊(n + 1)^2 / (1000 : ℝ)⌋ := by
            norm_cast
            apply Int.toNat_of_nonneg
            apply Int.floor_nonneg.mpr
            rw [@div_nonneg_iff]
            apply Or.inl
            constructor
            . norm_cast
              exact sq_nonneg (n + 1)
            . positivity
          rw [this]
          have : ⌊n ^ 2 / (1000 : ℝ)⌋.toNat = ⌊n ^ 2 / (1000 : ℝ)⌋ := by
            apply Int.toNat_of_nonneg
            apply Int.floor_nonneg.mpr
            rw [@div_nonneg_iff]
            apply Or.inl
            constructor
            . norm_cast
              exact sq_nonneg n
            . positivity
          by_cases h₂: n ≤ 499
          rw [this]
          simp
          rw [← @Int.floor_int_add]
          simp
          constructor
          apply Int.floor_le_floor
          linarith [hn n h₂]
          apply Int.floor_le_floor
          refine (div_le_div_iff ?pos.right.hab.hb' ?pos.right.hab.hd').mpr ?pos.right.hab.a'
          linarith
          linarith
          simp
          refine
            (pow_le_pow_iff_left ?pos.right.hab.a'.ha ?pos.right.hab.a'.hb
                  ?pos.right.hab.a'.hn).mpr
              ?pos.right.hab.a'.a
          linarith
          linarith
          linarith
          linarith
          simp at h₂
          have h₁: n = 500 := by linarith
          rw [h₁]
          norm_num
        -- norm_num at hn
        have n0: f 0 = 0 := by rw [hf 0]; norm_num
        have n1: f 1 = 0 := by rw [hf 1]; norm_num
        have n500: f 500 = 250 := by rw [hf 500]; norm_num
        -- we can find a number n such that f(n) = x, because f is strictly increasing, and
        -- every step of f is less than 1, so we can find a number n such that f(n) = x
        intro hx
        have (f : ℕ → ℤ) (n m : ℕ) (hn': n ≤ 500) (f_incr : ∀ n ≤ 500, 0 ≤ f (n + 1) - f n ∧ f (n + 1) - f n ≤ 1)
          (f0 : f 0 = 0) (fn : f n = m) :
          ∀ x, 0 ≤ x → x ≤ m → ∃ y, 0 ≤ y ∧ y ≤ n ∧ f y = x := by
          revert m fn
          induction n with
          | zero =>
            simp
            intro m hm x hx
            omega
          | succ n ih =>
            intro m hm x h0 h1
            obtain ⟨h2, h3⟩ := f_incr n (by linarith)
            have h4: f n = ↑m ∨ f n = ↑m - 1 := by omega
            rcases h4 with (h4 | h4)
            . -- f n = m
              specialize ih (by linarith) m h4 x h0 h1
              cases ih with | intro w h =>
              exists w
              omega
            -- f n = m - 1
            have h5: x = m ∨ x <= m - 1 := by omega
            rcases h5 with (h5 | h5)
            . -- x = m
              exists (n + 1)
              omega
            -- x <= m - 1
            have h6: m = 0 ∨ 1 ≤ m := by omega
            rcases h6 with (h6 | h6)
            . -- m = 0
              exists 0
              omega
            -- 1 ≤ m
            norm_cast at h4
            specialize ih (by linarith) (m - 1) h4 x h0 h5
            cases ih with | intro w h =>
            exists w
            omega
        specialize this f 500 250 (by linarith)
        simp at this hn
        have hn: ∀ n ≤ 500, f n ≤ f (n + 1) ∧ f (n + 1) ≤ 1 + f n := by
          intro n hn'
          specialize hn n hn'
          omega
        specialize this hn n0 n500 x hx
        rcases this with ⟨p, hp⟩
        have h1 : p = 0 ∨ 1 ≤ p := by omega
        rcases h1 with (h1 | h1)
        . -- p = 0
          use 1
          rw [h1] at hp
          simp at hp
          rw [n0, n1.symm, hf 1] at hp
          norm_cast at hp
          rw [hp.symm]
          simp
        use p
        have := hp.2
        rw [hf p] at this
        norm_cast at this
        norm_cast
        rw [this]
        omega

    rw [this]
    have : {x | x ≤ 250} = Finset.range 251 := by
      ext x
      simp
      constructor
      repeat intro hx; linarith
    rw [this, Set.ncard_coe_Finset, Finset.card_range]
  rw [a_ncard]

  -- From this point, the difference between $\frac{n^2}{1000}$ and $\frac{(n + 1)^2}{1000}$ is greater than 1, so all the numbers in the list \[\left\lfloor \frac{501^2}{1000} \right\rfloor, \ \left\lfloor \frac{502^2}{1000} \right\rfloor, \ \left\lfloor \frac{503^2}{1000} \right\rfloor, \ \dots, \ \left\lfloor \frac{1000^2}{1000} \right\rfloor\]are different.  Therefore, there are a total of $251 + 500 = \boxed{751}$ distinct numbers.
  have b_ncard : {x | ∃ (n : ℕ), 501 ≤ n ∧ n ≤ 1000 ∧ x = ⌊↑n ^ 2 / (1000 : ℝ)⌋.toNat}.ncard = 500 := by
    have p (a b : ℝ) (hab : 1 < a - b) : ⌊a⌋ ≠ ⌊b⌋ := by
      apply Ne.symm (Int.ne_of_lt _)
      have : b + 1 < a := by linarith
      rw [← Int.add_one_le_iff, Int.le_floor]
      apply le_trans
      case b => exact b + 1
      simp
      exact Int.floor_le b
      exact this.le
    have hn (n m : ℕ) (hn₁ : 501 ≤ n) (hm: m ≥ 1):
      ((n + m) ^ 2 / (1000 : ℝ)) - (n^2 / (1000 : ℝ)) > 1 := by
      field_simp
      have : (n + m: ℝ) ^ 2 - n^2 = 2 * n * m + m^2 := by linarith
      rw [this, one_lt_div (by positivity)]
      norm_cast
      apply lt_of_lt_of_le
      case b => exact 2 * n * 1 + 1^2
      simp
      linarith
      bound
    have hn (n m: ℕ) (hn₁ : 501 ≤ n) (hm: m ≥ 1)
        : (⌊↑(n + m) ^ 2 / (1000 : ℝ)⌋.toNat : ℤ) ≠ ⌊↑n ^ 2 / (1000 : ℝ)⌋.toNat := by
      have : ⌊↑(n + m) ^ 2 / (1000 : ℝ)⌋.toNat = ⌊↑(n + m) ^ 2 / (1000 : ℝ)⌋ := by
        apply Int.toNat_of_nonneg
        apply Int.floor_nonneg.mpr
        rw [@div_nonneg_iff]
        apply Or.inl
        constructor
        . norm_cast
          exact sq_nonneg (n + m)
        . positivity
      rw [this]
      have : ⌊↑n ^ 2 / (1000 : ℝ)⌋.toNat = ⌊↑n ^ 2 / (1000 : ℝ)⌋ := by
        apply Int.toNat_of_nonneg
        apply Int.floor_nonneg.mpr
        rw [@div_nonneg_iff]
        apply Or.inl
        constructor
        . norm_cast
          exact sq_nonneg n
        . positivity
      rw [this]
      apply p _ _
      simp
      exact hn n m hn₁ hm
    norm_cast at hn
    rw [Set.ncard_eq_of_bijective]
    -- (i : ℕ) → i < 500 → ℕ
    exact fun (i : ℕ) (hi : i < 500) => ⌊(i + 501) ^ 2 / (1000 : ℝ)⌋.toNat
    simp
    intro x a ha₁ ha₂ hx
    use a - 501
    constructor
    . have : a - 501 ≤ 499 := by exact Nat.sub_le_of_le_add ha₂
      linarith
    norm_cast
    rw [Nat.sub_add_cancel ha₁]
    norm_cast at hx
    exact hx.symm

    intro i hi
    simp
    use i + 501
    simp
    linarith

    intro i j hi hj hij
    by_contra! h
    by_cases hd: i < j
    . have : ∃d, 1 ≤ d ∧ d = j - i := by
        use j - i
        constructor
        . exact Nat.le_sub_of_add_le' hd
        . rfl
      rcases this with ⟨d, hd₁, hd₂⟩
      specialize hn (i + 501) d (by linarith) hd₁
      rw [hd₂, add_comm, ←add_assoc, Nat.sub_add_cancel hd.le] at hn
      absurd hn
      linarith
    simp at hd
    have hd: j < i := by
      exact Nat.lt_of_le_of_ne hd (id (Ne.symm h))
    have : ∃d, 1 ≤ d ∧ d = i - j := by
        use i - j
        constructor
        . exact Nat.le_sub_of_add_le' hd
        . rfl
    rcases this with ⟨d, hd₁, hd₂⟩
    specialize hn (j + 501) d (by linarith) hd₁
    have : j + 501 + (i - j) = i + 501 := by omega
    rw [hd₂, this] at hn
    absurd hn
    linarith
  rw [b_ncard]
