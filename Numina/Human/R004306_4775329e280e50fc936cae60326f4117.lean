import Mathlib

-- the name says it all
-- it takes two points on plane and the value of distance between them
-- and translates it to the pythagorean law, but without square roots

lemma pythagorean_law (x y: EuclideanSpace ℝ (Fin 2)) (d: ℝ) (H: dist x y = d):
    (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = d ^ 2 := by
  rw [EuclideanSpace.dist_eq] at H
  simp only [dist, sq_abs, Fin.sum_univ_two, Fin.isValue] at H
  rw [<- H, Real.sq_sqrt]
  nlinarith

lemma no_square_is_2_mod_4 (u w: ℤ) (H: u ^ 2 = 4 * w + 2): False := by
  obtain H0 | H0 := Int.even_or_odd u
  . obtain ⟨d, H0⟩ := H0
    rw [H0] at H
    ring_nf at H
    omega
  . obtain ⟨d, H0⟩ := H0
    rw [H0] at H
    ring_nf at H
    omega

lemma no_square_is_3_mod_4 (u w: ℤ) (H: u ^ 2 = 4 * w + 3): False := by
  obtain H0 | H0 := Int.even_or_odd u
  . obtain ⟨d, H0⟩ := H0
    rw [H0] at H
    ring_nf at H
    omega
  . obtain ⟨d, H0⟩ := H0
    rw [H0] at H
    ring_nf at H
    omega

lemma square_of_odd_is_1_mod_4 (u: ℤ) (H: Odd u): ∃ (w: ℤ), u ^ 2 = 4 * w + 1 := by
  obtain ⟨d, H⟩ := H
  rw [H]
  use (d ^ 2 + d)
  ring


/- [Example 4.5.7] Prove: If the side lengths of a rectangle are odd, then there does not exist a point inside it such that its distances to the four vertices are all integers. -/
theorem number_theory_250971 (p q : ℕ) (hp : Odd p) (hq : Odd q)
    (h : ∃ (x y: ℝ), 0 < x ∧ 0 < y ∧ x < (p: ℝ) ∧ y < (q: ℝ) ∧
      ∃ a b c d : ℤ,
      dist !₂[x, y] !₂[0, 0] = a ∧
      dist !₂[x, y] !₂[0, q] = b ∧
      dist !₂[x, y] !₂[p, q] = c ∧
      dist !₂[x, y] !₂[p, 0] = d) :
    False := by

  -- deconstruct the `h` to get all infornation out of it
  obtain ⟨x, y, Hx0, Hy0, Hx1, Hy1, a, b, c, d, Hd1, Hd2, Hd3, Hd4⟩ := h

  -- get the useful information out of all distance values
  apply pythagorean_law at Hd1
  apply pythagorean_law at Hd2
  apply pythagorean_law at Hd3
  apply pythagorean_law at Hd4
  simp at *

  -- introduce two auxiliary variables
  -- and use them everywhere
  set x' := (p: ℝ) - x
  set y' := (q: ℝ) - y
  rw [show (x - (p: ℝ)) ^ 2 = x' ^ 2 by unfold x'; ring] at Hd3 Hd4
  rw [show (y - (q: ℝ)) ^ 2 = y' ^ 2 by unfold y'; ring] at Hd2 Hd3

  ----------------------------------
  -- now some calculcations begin --
  ----------------------------------

  have eq1: y ^ 2 - y' ^ 2 = (a: ℝ) ^ 2 - (b: ℝ) ^ 2 := by
    linarith

  rw [sq_sub_sq y y'] at eq1
  rw [show y + y' = (q: ℝ) by simp only [add_sub_cancel, y']] at eq1
  apply_fun (fun w => (p: ℝ) * w) at eq1

  have eq2: (p: ℝ) * (q: ℝ) * (y + y') = (p: ℝ) * (q: ℝ) ^ 2 := by
    rw [sq, <- mul_assoc]
    congr 2
    simp [y']

  have eq3: x ^ 2 - x' ^ 2 = (b: ℝ) ^ 2 - (c: ℝ) ^ 2 := by
    linarith

  rw [sq_sub_sq x x'] at eq3
  rw [show x + x' = (p: ℝ) by simp only [add_sub_cancel, x']] at eq3
  apply_fun (fun w => (q: ℝ) * w) at eq3

  have eq4: (q: ℝ) * (p: ℝ) * (x + x') = (q: ℝ) * (p: ℝ) ^ 2 := by
    rw [sq, <- mul_assoc]
    congr 3
    simp [x']

  have eq5: 2 * x * (p: ℝ) * (q: ℝ) = (p: ℝ) ^ 2 * (q: ℝ) + ((b: ℝ) ^ 2 - (c: ℝ) ^ 2) * (q: ℝ) := by
    have H4 := Mathlib.Tactic.LinearCombination.add_eq_eq eq3 eq4
    ring_nf at H4 ⊢
    rw [H4]

  have eq6: 2 * x' * (p: ℝ) * (q: ℝ) = (q: ℝ) * (p: ℝ) ^ 2 - (q: ℝ) * ((b: ℝ) ^ 2 - (c: ℝ) ^ 2) := by
    have H4 := Mathlib.Tactic.LinearCombination'.sub_pf eq4 eq3
    ring_nf at H4 ⊢
    rw [H4]

  have eq7: 2 * y * (p: ℝ) * (q: ℝ) = (p: ℝ) * (q: ℝ) ^ 2 + (p: ℝ) * ((a: ℝ) ^ 2 - (b: ℝ) ^ 2) := by
    have H4 := Mathlib.Tactic.LinearCombination.add_eq_eq eq1 eq2
    ring_nf at H4 ⊢
    rw [H4]

  have eq8: 2 * y' * (p: ℝ) * (q: ℝ) = (p: ℝ) * (q: ℝ) ^ 2 - (p: ℝ) * ((a: ℝ) ^ 2 - (b: ℝ) ^ 2) := by
    have H4 := Mathlib.Tactic.LinearCombination'.sub_pf eq2 eq1
    ring_nf at H4 ⊢
    rw [H4]

  -------------------------------------------------------------------------
  -- now deductions about different quantities being integers etc. start --
  -------------------------------------------------------------------------

  -- first: if `x * p * q` is integer, then so is also `x' * p * q`

  have H1: (∃ (k_xpq: ℤ), x * (p: ℝ) * (q: ℝ) = (k_xpq: ℝ)) →
           (∃ (k_x'pq: ℤ), x' * (p: ℝ) * (q: ℝ) = (k_x'pq: ℝ)) := by
      rintro ⟨k, H2⟩
      use ((q: ℤ) * (p: ℤ) ^ 2 - k)
      simp
      rw [<- H2]
      ring_nf

  -- and here too: if `y * p * q` is integer, then so is also `y' * p * q`

  have H2: (∃ (k_ypq: ℤ), y * (p: ℝ) * (q: ℝ) = (k_ypq: ℝ)) →
           (∃ (k_y'pq: ℤ), y' * (p: ℝ) * (q: ℝ) = (k_y'pq: ℝ)) := by
      rintro ⟨k, H3⟩
      use ((p: ℤ) * (q: ℤ) ^ 2 - k)
      simp
      rw [<- H3]
      ring_nf

  -- now here we tak look two options:
  -- 1) both `x * p * q` and `y * p * q` are integers
  -- 2) at least one of them is not an integer

  obtain ⟨H3, H4⟩ | H3 := em ((∃ (k_xpq: ℤ), x * (p: ℝ) * (q: ℝ) = (k_xpq: ℝ)) ∧
                              ∃ (k_ypq: ℤ), y * (p: ℝ) * (q: ℝ) = (k_ypq: ℝ))

  . -- in this case it follows that all four expressions:
    -- `x * p * q`, `x' * p * q`, `y * p * q`, `y' * p * q`
    -- are integers

    have H5 := H1 H3
    have H6 := H2 H4

    obtain ⟨k_xpq, H3⟩ := H3
    obtain ⟨k_ypq, H4⟩ := H4
    obtain ⟨k_x'pq, H5⟩ := H5
    obtain ⟨k_y'pq, H6⟩ := H6

    -- we prove that `x * p * q` is odd integer or `x' * p * q` is odd integer

    have H7: Odd k_xpq ∨ Odd k_x'pq := by
      have aux: Odd (q * p ^ 2) := Odd.mul hq (Odd.pow hp)
      have aux0: (k_xpq: ℝ) + (k_x'pq: ℝ) = (q: ℝ) * (p: ℝ) ^ 2 := by
        rw [<- eq4, left_distrib, <- H3, <- H5]
        ring
      have aux1: Odd (k_xpq + k_x'pq) := by
        obtain ⟨d, aux⟩ := aux
        use d
        norm_cast
        rw [<- aux]
        simp
        norm_cast at aux0
      rw [Int.odd_add] at aux1
      rw [aux1]
      exact Int.even_or_odd k_x'pq

    -- we prove that `x * p * q` is odd integer or `x' * p * q` is odd integer

    have H8: Odd k_ypq ∨ Odd k_y'pq := by
      have aux: Odd (p * q ^ 2) := Odd.mul hp (Odd.pow hq)
      have aux0: (k_ypq: ℝ) + (k_y'pq: ℝ) = (p: ℝ) * (q: ℝ) ^ 2 := by
        rw [<- eq2, left_distrib, <- H4, <- H6]
        ring
      have aux1: Odd (k_ypq + k_y'pq) := by
        obtain ⟨d, aux⟩ := aux
        use d
        norm_cast
        rw [<- aux]
        simp
        norm_cast at aux0
      rw [Int.odd_add] at aux1
      rw [aux1]
      exact Int.even_or_odd k_y'pq

    -- now we take a look at all four possibilities,
    -- that we get by destructing disjunctions in `H7` and `H8`

    obtain H7 | H7 := H7 <;> obtain H8 | H8 := H8

    . -- first we prove that `(x * p * q) ^ 2 + (y * p * q) ^ 2 = (a * p * q) ^ 2`

      have H9: (k_xpq: ℝ) ^ 2 + (k_ypq: ℝ) ^ 2 = ((a: ℝ) * (p: ℝ) * (q: ℝ)) ^ 2 := by
        rw [<- H3, <- H4]
        rw [show (x * ↑p * ↑q) ^ 2 + (y * ↑p * ↑q) ^ 2 =
                  (x ^ 2 + y ^ 2) * (p: ℝ) ^ 2 * (q: ℝ) ^ 2 by ring]
        rw [Hd1]
        ring

      -- we know that `x * p * q` is odd integer,
      -- that means that `(x * p * q) ^ 2` is `1 (mod 4)`.
      -- the same with `(y * p * q) ^ 2`, which is also `1 (mod 4)`.
      -- so, it folows that `(a * p * q) ^ 2` is `2 (mod 4)`, which is impossible

      -- the same idea goes on in another three cases, with minimal changes

      obtain ⟨u, H10⟩ := square_of_odd_is_1_mod_4 _ H7
      obtain ⟨w, H11⟩ := square_of_odd_is_1_mod_4 _ H8
      rw [show (k_xpq: ℝ) ^ 2 = ↑(k_xpq ^ 2) by norm_cast, H10] at H9
      rw [show (k_ypq: ℝ) ^ 2 = ↑(k_ypq ^ 2) by norm_cast, H11] at H9
      norm_cast at H9
      rw [show (4 * u + 1 + (4 * w + 1)) = 4 * (u + w) + 2 by ring] at H9
      symm at H9
      apply no_square_is_2_mod_4 at H9
      exact H9

    . have H9: (k_xpq: ℝ) ^ 2 + (k_y'pq: ℝ) ^ 2 = ((b: ℝ) * (p: ℝ) * (q: ℝ)) ^ 2 := by
        rw [<- H3, <- H6]
        rw [show (x * ↑p * ↑q) ^ 2 + (y' * ↑p * ↑q) ^ 2 =
                  (x ^ 2 + y' ^ 2) * (p: ℝ) ^ 2 * (q: ℝ) ^ 2 by ring]
        rw [Hd2]
        ring

      obtain ⟨u, H10⟩ := square_of_odd_is_1_mod_4 _ H7
      obtain ⟨w, H11⟩ := square_of_odd_is_1_mod_4 _ H8
      rw [show (k_xpq: ℝ) ^ 2 = ↑(k_xpq ^ 2) by norm_cast, H10] at H9
      rw [show (k_y'pq: ℝ) ^ 2 = ↑(k_y'pq ^ 2) by norm_cast, H11] at H9
      norm_cast at H9
      rw [show (4 * u + 1 + (4 * w + 1)) = 4 * (u + w) + 2 by ring] at H9
      symm at H9
      apply no_square_is_2_mod_4 at H9
      exact H9

    . have H9: (k_x'pq: ℝ) ^ 2 + (k_ypq: ℝ) ^ 2 = ((d: ℝ) * (p: ℝ) * (q: ℝ)) ^ 2 := by
        rw [<- H5, <- H4]
        rw [show (x' * ↑p * ↑q) ^ 2 + (y * ↑p * ↑q) ^ 2 =
                  (x' ^ 2 + y ^ 2) * (p: ℝ) ^ 2 * (q: ℝ) ^ 2 by ring]
        rw [Hd4]
        ring

      obtain ⟨u, H10⟩ := square_of_odd_is_1_mod_4 _ H7
      obtain ⟨w, H11⟩ := square_of_odd_is_1_mod_4 _ H8
      rw [show (k_x'pq: ℝ) ^ 2 = ↑(k_x'pq ^ 2) by norm_cast, H10] at H9
      rw [show (k_ypq: ℝ) ^ 2 = ↑(k_ypq ^ 2) by norm_cast, H11] at H9
      norm_cast at H9
      rw [show (4 * u + 1 + (4 * w + 1)) = 4 * (u + w) + 2 by ring] at H9
      symm at H9
      apply no_square_is_2_mod_4 at H9
      exact H9

    . have H9: (k_x'pq: ℝ) ^ 2 + (k_y'pq: ℝ) ^ 2 = ((c: ℝ) * (p: ℝ) * (q: ℝ)) ^ 2 := by
        rw [<- H5, <- H6]
        rw [show (x' * ↑p * ↑q) ^ 2 + (y' * ↑p * ↑q) ^ 2 =
                  (x' ^ 2 + y' ^ 2) * (p: ℝ) ^ 2 * (q: ℝ) ^ 2 by ring]
        rw [Hd3]
        ring

      obtain ⟨u, H10⟩ := square_of_odd_is_1_mod_4 _ H7
      obtain ⟨w, H11⟩ := square_of_odd_is_1_mod_4 _ H8
      rw [show (k_x'pq: ℝ) ^ 2 = ↑(k_x'pq ^ 2) by norm_cast, H10] at H9
      rw [show (k_y'pq: ℝ) ^ 2 = ↑(k_y'pq ^ 2) by norm_cast, H11] at H9
      norm_cast at H9
      rw [show (4 * u + 1 + (4 * w + 1)) = 4 * (u + w) + 2 by ring] at H9
      symm at H9
      apply no_square_is_2_mod_4 at H9
      exact H9

  . -- now we know, that at least some of the expressions
    ---`x * p * q`, `x' * p * q`, `y * p * q`, `y' * p * q`
    -- are not an integer.
    -- but now we will prove that, if we double them, all of them are integers

    have H4: ∃ (k_2xpq: ℤ), 2 * x * (p: ℝ) * (q: ℝ) = (k_2xpq: ℝ) := by
      rw [eq5]
      norm_cast
      simp

    have H5: ∃ (k_2x'pq: ℤ), 2 * x' * (p: ℝ) * (q: ℝ) = (k_2x'pq: ℝ) := by
      rw [eq6]
      norm_cast
      simp

    have H6: ∃ (k_2ypq: ℤ), 2 * y * (p: ℝ) * (q: ℝ) = (k_2ypq: ℝ) := by
      rw [eq7]
      norm_cast
      simp

    have H7: ∃ (k_2y'pq: ℤ), 2 * y' * (p: ℝ) * (q: ℝ) = (k_2y'pq: ℝ) := by
      rw [eq8]
      norm_cast
      simp

    obtain ⟨k_2xpq, H4⟩ := H4
    obtain ⟨k_2x'pq, H5⟩ := H5
    obtain ⟨k_2ypq, H6⟩ := H6
    obtain ⟨k_2y'pq, H7⟩ := H7

    rw [not_and_or] at H3
    obtain H3 | H3 := H3

    -- now there are two possible values (`x * p * q` or `y * p * q`) that are not integers
    -- we will look at these two possibilities, and prove the `False` in both of them

    . simp at H3

      -- now we will look at two possiblities again:
      -- 1) `2 * x * p * q` is an even integer;
      -- 2) or it is an odd integer.
      -- and in both cases we will prove the necessary contradiction

      obtain H9 | H9 := Int.even_or_odd k_2xpq

      . -- as it happens, the expression `2 * x * p * q` being an even integer
        -- leads to `x * p * q` being an integer too,
        -- but that leads to contradiction

        obtain ⟨d, H9⟩ := H9
        have H10 := H3 d
        rw [H9] at H4
        simp at H4
        apply H10
        linarith

      . -- now let's take a look at the other case, when it is an odd integer

        have eq9: (2 * x * (p: ℝ) * (q: ℝ)) ^ 2 + (2 * y * (p: ℝ) * (q: ℝ)) ^ 2 =
                  (2 * (a: ℝ) * (p: ℝ) * (q: ℝ)) ^ 2 := by
          ring_nf
          rw [<- Hd1]
          ring_nf

        -- the first summand in the `eq9` is `1 (mod 4)`,
        -- the sum is obviously `0 (mod 4)`,
        -- and that means that the second summand must be `3 (mod 4)`.
        -- that's impossible for the square of supposedly integer value

        obtain ⟨d, H9⟩ := H9
        rw [H9] at H4
        rw [H4, H6] at eq9
        norm_cast at eq9
        ring_nf at eq9
        have eq10: k_2ypq ^ 2 = (a ^ 2 * ↑p ^ 2 * ↑q ^ 2 * 4) - (1 + d * 4 + d ^ 2 * 4) :=
          Eq.symm (sub_eq_of_eq_add' eq9.symm)
        rw [show a ^ 2 * (p: ℤ) ^ 2 * (q: ℤ) ^ 2 * 4 - (1 + d * 4 + d ^ 2 * 4) =
                 4 * (a ^ 2 * (p: ℤ) ^ 2 * (q: ℤ) ^ 2 - 1 - d - d ^ 2) + 3 by ring_nf] at eq10

        apply no_square_is_3_mod_4 at eq10
        exact eq10

    . simp at H3

      -- here the same idea as in the first case just above

      obtain H9 | H9 := Int.even_or_odd k_2ypq

      . obtain ⟨d, H9⟩ := H9
        have H10 := H3 d
        rw [H9] at H6
        simp at H6
        apply H10
        linarith

      . have eq9: (2 * x * (p: ℝ) * (q: ℝ)) ^ 2 + (2 * y * (p: ℝ) * (q: ℝ)) ^ 2 =
                  (2 * (a: ℝ) * (p: ℝ) * (q: ℝ)) ^ 2 := by
          ring_nf
          rw [<- Hd1]
          ring_nf

        obtain ⟨d, H9⟩ := H9
        rw [H9] at H6
        rw [H4, H6] at eq9
        norm_cast at eq9
        ring_nf at eq9
        have eq10: k_2xpq ^ 2 = (a ^ 2 * ↑p ^ 2 * ↑q ^ 2 * 4) - (1 + d * 4 + d ^ 2 * 4) := by
          linarith
        rw [show a ^ 2 * (p: ℤ) ^ 2 * (q: ℤ) ^ 2 * 4 - (1 + d * 4 + d ^ 2 * 4) =
                 4 * (a ^ 2 * (p: ℤ) ^ 2 * (q: ℤ) ^ 2 - 1 - d - d ^ 2) + 3 by ring_nf] at eq10

        apply no_square_is_3_mod_4 at eq10
        exact eq10