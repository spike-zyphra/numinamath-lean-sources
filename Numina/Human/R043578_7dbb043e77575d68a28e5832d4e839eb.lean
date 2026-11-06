import Mathlib

open Classical

/- Let $k$ be a positive integer. Prove that the number $\left(4 k^{2}-1\right)^{2}$ has a positive divisor of the form $8 k n-1$ if and only if $k$ is even.  (United Kingdom) -/
theorem number_theory_23709 (k : ℕ) (hk : 0 < k) :
    (∃ d, 0 < d ∧ d ∣ (4 * k ^ 2 - (1 : ℤ)) ^ 2 ∧ ∃ n, d = 8 * k * n - (1 : ℤ)) ↔ Even k := by
  -- The statement follows from the following fact.
  -- Lemma. For arbitrary positive integers $x$ and $y$, the number $4 x y-1$ divides $\left(4 x^{2}-1\right)^{2}$ if and only if $x=y$.
  suffices hlem {x y : ℤ} (hx : x > 0) (hy : y > 0) : 4 * x * y - 1 ∣ (4 * x ^ 2 - 1) ^ 2 ↔ x = y
  · -- To prove the problem statement, apply the Lemma for $x=k$ and $y=2 n$;
    -- the number $8 k n-1$ divides $\left(4 k^{2}-1\right)^{2}$ if and only if $k=2 n$.
    --  Hence, there is no such $n$ if $k$ is odd and $n=k / 2$ is the only solution if $k$ is even.
    constructor <;> intro h
    · obtain ⟨d, hdpos, hdvd, n, hdn⟩ := h
      have hnpos : n > 0 := by
        rw [hdn] at hdpos
        apply sub_pos.mp at hdpos
        have : 8 * k * n > 0 := by apply lt_trans ?_ hdpos; simp
        exact lt_of_nsmul_lt_nsmul_right (8 * k) this
      lift n to ℕ using le_of_lt hnpos
      obtain h := hlem (x := k) (y := 2 * n) (by norm_cast) (by apply mul_pos; trivial; exact hnpos)
      rw [hdn] at hdvd
      have : 4 * ↑k * (2 * ↑n) - (1 : ℤ) ∣ (4 * ↑k ^ 2 - (1 : ℤ)) ^ 2 := by
        apply dvd_trans ?_ hdvd
        apply dvd_of_eq
        ring
      apply h.mp at this
      norm_cast at this
      use n
      rw [this]
      ring
    · use 4 * k ^ 2 - (1 : ℤ)
      split_ands
      · apply sub_pos.mpr
        apply lt_of_lt_of_le (b := 4 * 1)
        · trivial
        · apply mul_le_mul_of_nonneg_left
          · apply one_le_pow_iff_of_nonneg ?_ ?_ |>.mpr
            · norm_cast
            · norm_cast; exact le_of_lt hk
            · trivial
          · trivial
      · apply dvd_pow_self
        trivial
      · obtain ⟨n, hk⟩ := h
        use n
        rw [hk]
        norm_cast
        ring_nf
  · -- Proof. If $x=y$ then $4 x y-1=4 x^{2}-1$ obviously divides $\left(4 x^{2}-1\right)^{2}$ so it is sufficient to consider the opposite direction.
    constructor <;> intro h
    on_goal 2 =>
      rw [h]
      apply dvd_pow
      · apply dvd_of_eq
        ring
      · trivial
    · -- Call a pair $(x, y)$ of positive integers bad if $4 x y-1$ divides $\left(4 x^{2}-1\right)^{2}$ but $x \neq y$.
      let bad (x y : ℤ) := 4 * x * y - (1 : ℤ) ∣ (4 * x ^ 2 - (1 : ℤ)) ^ 2 ∧ x ≠ y
      -- In order to prove that bad pairs do not exist, we present two properties of them which provide an infinite descent.
      -- Property (i). If $(x, y)$ is a bad pair and $x&lt;y$ then there exists a positive integer $z&lt;x$ such that $(x, z)$ is also bad.
      have P₁ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hb : bad x y) (hlt : x < y) : ∃ z > 0, z < x ∧ bad x z := by
        -- Let $r=\frac{\left(4 x^{2}-1\right)^{2}}{4 x y-1}$.
        obtain ⟨r, hr⟩ := hb.1
        -- Then $$ r=-r \cdot(-1) \equiv-r(4 x y-1)=-\left(4 x^{2}-1\right)^{2} \equiv-1 \quad(\bmod 4 x) $$
        have hrmod : r ≡ -1 [ZMOD 4 * x] := by
          trans -r * (0 - 1)
          · congr; ring
          trans -r * (4 * x * y - 1)
          · apply Int.ModEq.mul_left
            apply Int.ModEq.sub_right
            apply Int.modEq_of_dvd
            rw [sub_zero]
            exact Int.dvd_mul_right (4 * x) y
          trans -((4 * x * y - 1) * r)
          · congr 1; ring
          · rw [←hr]
            apply Int.ModEq.neg
            trans (0 - 1) ^ 2
            · apply Int.ModEq.pow
              apply Int.ModEq.sub_right
              apply Int.modEq_of_dvd
              rw [zero_sub, dvd_neg]
              use x
              ring
            · congr
        --  and $r=4 x z-1$ with some positive integer $z$.
        apply Int.ModEq.symm at hrmod
        apply Int.modEq_iff_dvd.mp at hrmod
        obtain ⟨z, hz⟩ := hrmod
        have hpos : 0 < 4 * x * y - 1 := by
          apply lt_of_lt_of_le (b := 4 * 1 * 1 - 1)
          · trivial
          · apply sub_le_sub_right
            apply mul_le_mul
            · apply mul_le_mul_of_nonneg_left
              · exact hx
              · trivial
            · exact hy
            · trivial
            · apply mul_nonneg
              · trivial
              · exact le_of_lt hx
        use z
        -- From $x&lt;y$ we obtain that $$ 4 x z-1=\frac{\left(4 x^{2}-1\right)^{2}}{4 x y-1}&lt;4 x^{2}-1 $$
        have hzltx : z < x := by
          have : 4 * x * z - 1 < 4 * x * x - 1 := by
            apply lt_of_eq_of_lt (b := (4 * x ^ 2 - 1) ^ 2 / (4 * x * y - 1))
            · rw [hr, ←hz, mul_div_cancel_left₀]
              · ring
              · apply ne_of_gt hpos
            · refine (Int.ediv_lt_iff_lt_mul hpos).mpr ?h₂.a
              rw [sq]
              apply mul_lt_mul_of_le_of_lt_of_pos_of_nonneg
              · apply le_of_eq
                ring
              · apply Int.sub_lt_sub_right
                rw [sq, ←mul_assoc]
                apply Int.mul_lt_mul_of_pos_left
                · exact hlt
                · apply mul_pos
                  · trivial
                  · exact hx
              · apply sub_pos.mpr
                apply lt_of_lt_of_le (b := 4 * 1)
                · trivial
                · apply mul_le_mul_of_nonneg_left
                  · exact one_le_pow₀ hx
                  · trivial
              · exact le_of_lt hpos
          -- and therefore $z&lt;x$.
          apply Int.lt_of_sub_lt_sub_right at this
          apply Int.lt_of_mul_lt_mul_left this
          apply mul_nonneg
          · trivial
          · exact le_of_lt hx
        split_ands
        · apply pos_of_mul_pos_right (a := 4 * x)
          · rw [←hz]
            apply sub_pos.mpr
            suffices : r ≥ 0
            · exact this
            · apply nonneg_of_mul_nonneg_right (a := 4 * x * y - 1)
              · rw [←hr]
                exact sq_nonneg (4 * x ^ 2 - 1)
              · exact hpos
          · apply mul_nonneg
            · trivial
            · exact le_of_lt hx
        · exact hzltx
        . -- By the construction, the number $4 x z-1$ is a divisor of $\left(4 x^{2}-1\right)^{2}$ so $(x, z)$ is a bad pair.
          rw [←hz]
          simp only [Int.reduceNeg, sub_neg_eq_add, add_sub_cancel_right]
          rw [hr]
          exact Int.dvd_mul_left (4 * x * y - 1) r
        · exact ne_of_gt hzltx
      -- Property (ii). If $(x, y)$ is a bad pair then $(y, x)$ is also bad.
      have P₂ {x y : ℤ} (hb : bad x y) : bad y x := by
        unfold bad
        constructor
        on_goal 2 =>
          obtain h := hb.2
          exact id (Ne.symm h)
        · -- Since $1=1^{2} \equiv(4 x y)^{2}(\bmod 4 x y-1)$,
          have : 1 ≡ (4 * x * y) ^ 2 [ZMOD (4 * x * y - 1)] := by
            trans 1 ^ 2
            · trivial
            · refine Int.ModEq.pow 2 ?_
              apply Int.modEq_of_dvd
              exact Int.dvd_refl (4 * x * y - 1)
          -- we have $$ \left(4 y^{2}-1\right)^{2} \equiv\left(4 y^{2}-(4 x y)^{2}\right)^{2}=16 y^{4}\left(4 x^{2}-1\right)^{2} \equiv 0 \quad(\bmod 4 x y-1) $$
          have : (4 * y ^ 2 - 1) ^ 2 ≡ 0 [ZMOD (4 * x * y - 1)] := by
            trans (4 * y ^ 2 - (4 * x * y) ^ 2) ^ 2
            · apply Int.ModEq.pow
              apply Int.ModEq.sub_left
              exact this
            trans 16 * y ^ 4 * (4 * x ^ 2 - 1) ^ 2
            · congr
              ring
            · apply Int.modEq_of_dvd
              rw [zero_sub, dvd_neg]
              apply dvd_mul_of_dvd_right
              exact hb.1
          -- Hence, the number $4 x y-1$ divides $\left(4 y^{2}-1\right)^{2}$ as well.
          trans 4 * x * y - 1
          · apply dvd_of_eq
            ring
          · exact Int.dvd_of_emod_eq_zero this
      -- Now suppose that there exists at least one bad pair.
      by_contra hne
      have hp : ∃ n : ℕ, ∃ x y : ℤ, 0 < x ∧ 0 < y ∧ bad x y ∧ n = 2 * x + y := by
        lift x to ℕ using le_of_lt hx
        lift y to ℕ using le_of_lt hy
        use 2 * x + y, x, y, hx, hy
        norm_cast
      -- Take a bad pair $(x, y)$ such that $2 x+y$ attains its smallest possible value.
      let r₀ := Nat.find hp
      have ⟨x, y, hxpos, hypos, hbad, hr₀⟩ : ∃ x y : ℤ, 0 < x ∧ 0 < y ∧ bad x y ∧ r₀ = 2 * x + y := Nat.find_spec hp
      lift x to ℕ using le_of_lt hxpos
      lift y to ℕ using le_of_lt hypos
      have hr₀ : r₀ = 2 * x + y := by exact Int.ofNat_inj.mp hr₀
      by_cases hxy : x < (y : ℤ)
      · -- If $x&lt;y$ then property (i) provides a bad pair $(x, z)$ with $z&lt;y$ and thus $2 x+z&lt;2 x+y$.
        obtain ⟨z, hzpos, hlt, hbadz⟩ := P₁ hxpos hypos hbad hxy
        lift z to ℕ using le_of_lt hzpos
        let r₁ : ℕ := 2 * x + z
        have hr₁ : r₁ < r₀ := by
          rw [hr₀]
          apply add_lt_add_left
          norm_cast at hxy hlt
          exact Nat.lt_trans hlt hxy
        apply Nat.find_min hp at hr₁
        push_neg at hr₁
        apply hr₁ x z hxpos hzpos at hbadz
        simp [r₁] at hbadz
      · -- Otherwise, if $y&lt;x$, property (ii) yields that pair $(y, x)$ is also bad while $2 y+x&lt;2 x+y$.
        obtain hbad' := P₂ hbad
        let r₁ : ℕ := 2 * y + x
        have hr₁ : r₁ < r₀ := by
          suffices : (r₁ : ℤ) < r₀
          · exact Int.ofNat_lt.mp this
          · apply lt_of_sub_pos
            rw [hr₀, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
            ring_nf
            apply sub_pos.mpr
            apply lt_of_le_of_ne
            · exact Int.not_lt.mp hxy
            · obtain h := hbad'.2
              exact h
        -- Both cases contradict the assumption that $2 x+y$ is minimal; the Lemma is proved.
        apply Nat.find_min hp at hr₁
        push_neg at hr₁
        apply hr₁ y x hypos hxpos at hbad'
        simp [r₁] at hbad'
