import Mathlib

/- The union of consecutive intervals is equal to a large interval. -/
lemma sUnion_Ico_eq {f : ℕ → ℝ} (hf : Monotone f) (n : ℕ)
  : ⋃₀ ((fun i : ℕ => Set.Ico (f i) (f (i + 1))) '' Set.Ico 0 n) = Set.Ico (f 0) (f n) := by
    -- we prove by induction on n, the number of intervals
    induction' n with n1 h1
    -- no intervals is trivially true
    · norm_num
    · have ico_succ : Set.Ico 0 (n1 + 1) = insert n1 (Set.Ico 0 n1) := by
        ext i
        norm_num
        omega

      -- apply induction hypothesis
      rw [ico_succ, Set.image_insert_eq, Set.sUnion_insert, h1]

      -- note that f(0) ≤ f(n1), because f is monotone
      have left_le : f 0 ≤ f n1 := by apply hf; omega
      -- so min(f(n1), f(0)) = f(0)
      have left_eq : f n1 ⊓ f 0 = f 0 := by norm_num [left_le]

      -- and f(n1) ≤ f(n1 + 1), because f is monotone
      have right_le : f n1 ≤ f (n1 + 1) := by apply hf; omega
      -- so max(f(n1 + 1), f(n1)) = f(n1 + 1)
      have right_eq : f (n1 + 1) ⊔ f n1 = f (n1 + 1) := by norm_num [right_le]

      -- union of intervals is interval
      rw [Set.Ico_union_Ico]

      -- simplify
      rw [left_eq, right_eq]

      -- the intervals were not disjoint
      · norm_num
      · norm_num

/- The union of pre-images of sets is equal to the pre-image of a union of sets. -/
lemma sunion_preimage (f : ℕ → ℝ) (g : ℕ → Set ℝ) (S : Set ℕ)
  : ⋃₀ ((fun i => f ⁻¹' g i) '' S) = f ⁻¹' ⋃₀ (g '' S) := by
    ext x
    simp only [Set.sUnion_image, Set.mem_iUnion, Set.mem_preimage, exists_prop, Set.preimage_iUnion]

/- If x_i is contained in (0, 1), and we split up (0, 1) into m intervals [k / m, (k + 1) / m)
  then one of the intervals has an infinite pre-image of x. -/
lemma exists_interval_infinite' {x : ℕ → ℝ}
  (hx : ∀ (n : ℕ), x n ∈ Set.Ico 0 1) (m : ℕ) [NeZero m]
  : ∃ k ∈ Finset.Icc (0 : ℕ) (m - 1), (x ⁻¹' (Set.Ico (k / m : ℝ) ((k + 1) / m : ℝ))).Infinite := by
    -- assume that all pre-images are finite
    by_contra nee

    --simplify
    norm_num at nee

    -- consider f(i) = i / m
    let f : ℕ → ℝ := (· / m)

    -- then f is monotone
    have f_mono : Monotone f := by
      intro a b hh
      norm_num [f]
      gcongr

    -- then f is the endpoints of our intervals. The union of the intervals is equal to (0, 1)
    have sUnion_eq := sUnion_Ico_eq f_mono m

    -- Then the union of pre-images is finite
    have inter_finite : (⋃₀ (((fun i => x ⁻¹' Set.Ico (f i) (f (i + 1))) '' Set.Ico 0 m))).Finite := by
      apply Set.Finite.sUnion
      -- we have a finite number of pre-images
      · apply Set.Finite.image
        exact Set.finite_Ico 0 m
      -- and each pre-image is finite
      · norm_num
        intro a ah
        norm_num [f]
        exact nee a (by omega)

    -- then the pre-image of x on (0, 1) is finite
    have pre_image_finite : (x ⁻¹' Set.Ico 0 1).Finite := by

      -- simplify union of intervals into single interval
      rw [sunion_preimage, sUnion_eq] at inter_finite

      -- endpoints are 0 and 1
      have f_0 : f 0 = 0 := by norm_num [f]
      have f_m : f m = 1 := by norm_num [f]

      rwa [f_0, f_m] at inter_finite


    -- but every value is contained in (0, 1)
    have range_subs : Set.range x ⊆ Set.Ico 0 1 := Set.range_subset_iff.mpr hx

    -- so the pre-image of x on (0, 1) is every natural number
    have interval_inter_eq : x ⁻¹' Set.Ico 0 1 = Set.univ
      := Set.preimage_eq_univ_iff.mpr range_subs
    rw [interval_inter_eq] at pre_image_finite

    -- but there are an infinite number of natural numbers
    have not_finite := Set.infinite_univ (α := ℕ)

    -- contradiction
    contradiction

/- (Bolzano-Weierstrass) Consider an infinite sequence of real numbers in the interval $[0,1[$ $x_{0}, x_{1}, x_{2}, \ldots$.

- Show that either the interval $\left[0, \frac{1}{2}\right[$ or the interval $\left[\frac{1}{2}, 1\right[$ contains an infinite number of elements of the sequence.
- Fix a natural number $n \geq 1$. Show that there exists an integer $k$ in the set $\left\{0,1,2, \ldots, 2^{n}-1\right\}$ such that the interval $\left[\frac{k}{2^{n}}, \frac{k+1}{2^{n}}\right[$ contains an infinite number of elements of the sequence. -/
theorem calculus_106855 (x : ℕ → ℝ)
  (hx : ∀ n, x n ∈ Set.Ico 0 1) (n : ℕ) :
  ((x ⁻¹' (Set.Ico 0 (1 / 2 : ℝ))).Infinite ∨ (x ⁻¹' (Set.Ico (1 / 2 : ℝ) 1)).Infinite)
  ∧ (∃ k ∈ Finset.Icc (0 : ℕ) (2 ^ n - 1),  (x ⁻¹' (Set.Ico (k / 2 ^ n : ℝ) ((k + 1) / 2 ^ n : ℝ))).Infinite) := by
    -- we prove the parts separately
    split_ands
    -- if we partition (0, 1) into two intervals, then there's one with an infinite pre-image
    · obtain ⟨k, k1, k2⟩ := exists_interval_infinite' hx 2

      -- it's either the first or second interval
      norm_num at k1

      -- so either the first is infinite, or the second is infinite
      interval_cases k <;> (norm_num at k2; tauto)

    -- if we partition (0, 1) into 2 ^ n intervals, then there's one with an infinite pre-image
    · have app := exists_interval_infinite' hx (2 ^ n)
      -- normalize
      simp only [Finset.mem_Icc, zero_le, true_and, Nat.cast_pow, Nat.cast_ofNat] at app ⊢

      -- that's what we wanted to prove
      exact app